/*
 * File:    credit_t_route.sv
 * Brief:   Routing decision logic for the T switch
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module credit_t_route
    import common_pkg::*;
#(
    parameter N             = DEFAULT_N,    // number of clients
    parameter A_W           = DEFAULT_A_W,  // log number of clients ($clog2(N) + 1)
    parameter posl          = 0,            // Vertical position in the NoC
    parameter posx          = 0,            // Horizontal position in the level
    parameter VC_W          = DEFAULT_VC_W,
    parameter VC_FIFO_DEPTH = DEFAULT_VC_FIFO_DEPTH,//Actual depth is this - 1
    parameter FAIR_VC_ARB   = 0             //Whether to use static VC prioritization or matrix arbiters
) (
    //Clock and reset
    input logic clk,    // clock
    input logic rst,    // reset

    //Datapath and control signals
    //Lower VCs are statically prioritized over higher VCs
    //So with VC_W == 2 for example, VC0 should be used as a "reply" VC and VC1 for "requests"
    input  logic [VC_W-1:0]             l_i_v,          // left input valid
    input  logic [VC_W-1:0]             r_i_v,          // right input valid
    input  logic [VC_W-1:0]             u0_i_v,         // up0 input valid
    output logic [VC_W-1:0]             l_i_bp,         // left input is backpressured
    output logic [VC_W-1:0]             r_i_bp,         // right input is backpressured
    output logic [VC_W-1:0]             u0_i_bp,        // up0 input is backpressured
    input  logic [VC_W-1:0][A_W-1:0]    l_i_addr,       // left input addr
    input  logic [VC_W-1:0][A_W-1:0]    r_i_addr,       // right input addr
    input  logic [VC_W-1:0][A_W-1:0]    u0_i_addr,      // up0 input addr
    output logic [VC_W-1:0]             l_o_v,          // valid for l mux
    output logic [VC_W-1:0]             r_o_v,          // valid for r mux
    output logic [VC_W-1:0]             u0_o_v,         // valid for u0 mux
    input  logic [VC_W-1:0]             l_o_credit_gnt, // left output credit grant
    input  logic [VC_W-1:0]             r_o_credit_gnt, // right output credit grant
    input  logic [VC_W-1:0]             u0_o_credit_gnt,// up0 output credit grant
    output logic [$clog2(VC_W*2)-1:0]   l_sel,          // select for l mux
    output logic [$clog2(VC_W*2)-1:0]   r_sel,          // select for r mux
    output logic [$clog2(VC_W*2)-1:0]   u0_sel          // select for u0 mux
    //For the mux selects, each half of the possible outputs indicates different VCs from the same input direction
);

/* ------------------------------------------------------------------------------------------------
 * Counters Instantiation, Backpressuring
 * --------------------------------------------------------------------------------------------- */

//Left, right, and up0 output backpressure signals, based on credit counts
logic [VC_W-1:0]    l_o_bp;
logic [VC_W-1:0]    r_o_bp;
logic [VC_W-1:0]    u0_o_bp;

logic [VC_W-1:0]                            l_has_credit, r_has_credit, u0_has_credit;
logic [VC_W-1:0][$clog2(VC_FIFO_DEPTH)-1:0] l_credits,    r_credits,    u0_credits;

credit_counters_tx #(
    .VC_W(VC_W),
    .DEPTH(VC_FIFO_DEPTH)
) l_counters_inst (
    //Clock and reset
    .i_clk(clk),
    .i_rst(rst),

    //Connection to the receiver
    .i_vc_credit_gnt(l_o_credit_gnt),

    //Interface for routing logic
    .i_vc_target(l_o_v),
    .o_credits(l_credits),
    //verilator lint_save
    //verilator lint_off PINCONNECTEMPTY
    .o_credits_next()//NU
    //verilator lint_restore
);

credit_counters_tx #(
    .VC_W(VC_W),
    .DEPTH(VC_FIFO_DEPTH)
) r_counters_inst (
    //Clock and reset
    .i_clk(clk),
    .i_rst(rst),

    //Connection to the receiver
    .i_vc_credit_gnt(r_o_credit_gnt),

    //Interface for routing logic
    .i_vc_target(r_o_v),
    .o_credits(r_credits),
    //verilator lint_save
    //verilator lint_off PINCONNECTEMPTY
    .o_credits_next()//NU
    //verilator lint_restore
);

credit_counters_tx #(
    .VC_W(VC_W),
    .DEPTH(VC_FIFO_DEPTH)
) u0_counters_inst (
    //Clock and reset
    .i_clk(clk),
    .i_rst(rst),

    //Connection to the receiver
    .i_vc_credit_gnt(u0_o_credit_gnt),

    //Interface for routing logic
    .i_vc_target(u0_o_v),
    .o_credits(u0_credits),
    //verilator lint_save
    //verilator lint_off PINCONNECTEMPTY
    .o_credits_next()//NU
    //verilator lint_restore
);

always_comb begin
    for (int ii = 0; ii < VC_W; ++ii) begin
        l_has_credit[ii]    = |l_credits[ii];
        r_has_credit[ii]    = |r_credits[ii];
        u0_has_credit[ii]   = |u0_credits[ii];

        l_o_bp[ii]  = !l_has_credit[ii];
        r_o_bp[ii]  = !r_has_credit[ii];
        u0_o_bp[ii] = !u0_has_credit[ii];
    end
end

/* ------------------------------------------------------------------------------------------------
 * Address Decoding Logic
 * --------------------------------------------------------------------------------------------- */

logic [VC_W-1:0]              l_wants_r, l_wants_u0;
logic [VC_W-1:0]  r_wants_l,             r_wants_u0;
logic [VC_W-1:0] u0_wants_l, u0_wants_r;

generate
for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_vc_addr_dec
    //Expressions for when the packet in VC ii wants to go in a certain direction (based on the address)

    assign l_wants_r[ii]  = l_i_v[ii] & l_i_addr[ii][posl] & (l_i_addr[ii][A_W-1:posl+1] == posx[A_W-posl-2:0]);
    assign l_wants_u0[ii] = l_i_v[ii] &                      (l_i_addr[ii][A_W-1:posl+1] != posx[A_W-posl-2:0]);

    assign r_wants_l[ii]  = r_i_v[ii] & ~r_i_addr[ii][posl] & (r_i_addr[ii][A_W-1:posl+1] == posx[A_W-posl-2:0]);
    assign r_wants_u0[ii] = r_i_v[ii] &                       (r_i_addr[ii][A_W-1:posl+1] != posx[A_W-posl-2:0]);

    assign u0_wants_l[ii] = u0_i_v[ii] & ~u0_i_addr[ii][posl];
    assign u0_wants_r[ii] = u0_i_v[ii] &  u0_i_addr[ii][posl];
end : gen_vc_addr_dec
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Direction Arbitration
 * --------------------------------------------------------------------------------------------- */

//We only RR arbitrate between left, right, and up0 since VCs are prioritized separately

//"Wins" means that either it is a given source direction's turn or no other
//source direction wants to go in that direction: it's not a grant because it
//doesn't take into account whether the source direction actually _wants_ it
logic             l_wins_r, l_wins_u0;
logic  r_wins_l,            r_wins_u0;
logic u0_wins_l, u0_wins_r;

typedef enum logic [1:0] {
    //Unlike the Pi switch, there is only one U
    L_TURN, R_TURN, U0_TURN
} state_e;//Whose "turn" it is

state_e state, next_state;

always @(posedge clk) begin
    if (rst) begin
        state <= L_TURN;
    end else begin
        state <= next_state;
    end
end

always_comb begin
    //Based on whose turn it was, and who is waiting, decide whose turn is next!
    next_state = state;//By default, if no one else is waiting the turn doesn't change
    case (state)
        //TODO revisit round-robining between higher priority VCs first instead of direction-first in the future
        L_TURN: begin
            if (|r_i_bp) begin
                next_state = R_TURN;
            end else if (|u0_i_bp) begin
                next_state = U0_TURN;
            end
        end
        R_TURN: begin
            if (|u0_i_bp) begin
                next_state = U0_TURN;
            end else if (|l_i_bp) begin
                next_state = L_TURN;
            end
        end
        U0_TURN: begin
            if (|l_i_bp) begin
                next_state = L_TURN;
            end else if (|r_i_bp) begin
                next_state = R_TURN;
            end
        end
        default: begin//Illegal state
            next_state = L_TURN;
        end
    endcase
end

assign  l_wins_r    = (state == L_TURN)  | ~(|u0_wants_r);
assign u0_wins_r    = (state == U0_TURN) | ~(| l_wants_r);

assign  r_wins_l    = (state == R_TURN)  | ~(|u0_wants_l);
assign u0_wins_l    = (state == U0_TURN) | ~(| r_wants_l);

assign l_wins_u0    = (state == L_TURN) | ~(|r_wants_u0);
assign r_wins_u0    = (state == R_TURN) | ~(|l_wants_u0);

/* ------------------------------------------------------------------------------------------------
 * VC Arbitration
 * --------------------------------------------------------------------------------------------- */

//_ Verilator _thinks_ there is a combinational loop here because we're
//using the same vectors, HOWEVER we are using different _bits_ of the
//vectors so this is not the case. Vivado synthesis confirms this.
//So just quiet Verilator since it is buggy
//verilator lint_save
//verilator lint_off UNOPTFLAT

logic [VC_W-1:0]             l_gets_r, l_gets_u0;
logic [VC_W-1:0]  r_gets_l,            r_gets_u0;
logic [VC_W-1:0] u0_gets_l, u0_gets_r;

//TODO free running counter decides what the "base" VC is in terms of priority?

generate
if (FAIR_VC_ARB) begin : gen_fair_vc_arb
    logic [VC_W-1:0]            l_req_r, l_req_u0;
    logic [VC_W-1:0]  r_req_l,           r_req_u0;
    logic [VC_W-1:0] u0_req_l, u0_req_r;

    //A VC only makes a request if:
    //- It wants to go in that direction
    //- The corresponding output direction's VC isn't backpressured
    //- Its source direction has "won" the output direction
    for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_vc_grant
        assign  l_req_r[ii] =  l_wants_r[ii] & ~r_o_bp[ii] &  l_wins_r;
        assign u0_req_r[ii] = u0_wants_r[ii] & ~r_o_bp[ii] & u0_wins_r;

        assign  r_req_l[ii] =  r_wants_l[ii] & ~l_o_bp[ii] &  r_wins_l;
        assign u0_req_l[ii] = u0_wants_l[ii] & ~l_o_bp[ii] & u0_wins_l;

        assign l_req_u0[ii] = l_wants_u0[ii] & ~u0_o_bp[ii] & l_wins_u0;
        assign r_req_u0[ii] = r_wants_u0[ii] & ~u0_o_bp[ii] & r_wins_u0;
    end : gen_vc_grant

    matrix_arbiter #(
        .NUM(VC_W)
    ) l_to_r_arbiter (
        .clk(clk),
        .rst(rst),

        .i_req(l_req_r),
        .o_gnt(l_gets_r)
    );

    matrix_arbiter #(
        .NUM(VC_W)
    ) l_to_u0_arbiter (
        .clk(clk),
        .rst(rst),

        .i_req(l_req_u0),
        .o_gnt(l_gets_u0)
    );

    matrix_arbiter #(
        .NUM(VC_W)
    ) r_to_l_arbiter (
        .clk(clk),
        .rst(rst),

        .i_req(r_req_l),
        .o_gnt(r_gets_l)
    );

    matrix_arbiter #(
        .NUM(VC_W)
    ) r_to_u0_arbiter (
        .clk(clk),
        .rst(rst),

        .i_req(r_req_u0),
        .o_gnt(r_gets_u0)
    );

    matrix_arbiter #(
        .NUM(VC_W)
    ) u0_to_l_arbiter (
        .clk(clk),
        .rst(rst),

        .i_req(u0_req_l),
        .o_gnt(u0_gets_l)
    );

    matrix_arbiter #(
        .NUM(VC_W)
    ) u0_to_r_arbiter (
        .clk(clk),
        .rst(rst),

        .i_req(u0_req_r),
        .o_gnt(u0_gets_r)
    );
end : gen_fair_vc_arb
else begin : gen_static_vc_arb
    //A VC "gets" granted access to an output direction if
    // - We want to go in that output direction
    // - We're not recieving output backpressure from that direction's corresponding VC
    // - It's our input direction's turn to go in that output direction,
    //   or no VC of any other input direction wants to use that output direction (our direction "wins")
    // - No lower-numbered VC has been granted access to that output direction
    //   (static priority of VCs from the same input direction)

    //Lower VCs are statically prioritized over higher VCs, so no need for that check for VC0
    assign  l_gets_r[0] =  l_wants_r[0] &  ~r_o_bp[0] &  l_wins_r;
    assign u0_gets_r[0] = u0_wants_r[0] &  ~r_o_bp[0] & u0_wins_r;

    assign  r_gets_l[0] =  r_wants_l[0] &  ~l_o_bp[0] &  r_wins_l;
    assign u0_gets_l[0] = u0_wants_l[0] &  ~l_o_bp[0] & u0_wins_l;

    assign l_gets_u0[0] = l_wants_u0[0] & ~u0_o_bp[0] &  l_wins_u0;
    assign r_gets_u0[0] = r_wants_u0[0] & ~u0_o_bp[0] &  r_wins_u0;

    //All other VCs do need that check
    for (genvar ii = 1; ii < VC_W; ++ii) begin : gen_vc_grant
        //FIXME there are cases where this may be inefficient!
        //Ex, if we want to go from right VC0 to left VC0, and up VC1 to left VC1, we will grant NEITHER
        //to access the left direction until it is their turn: ie. nothing will
        //happen when it is L's turn which wastes time!
        //This would have actually been a problem in the original RTL too, so perhaps we don't need to fix this...

        assign  l_gets_r[ii] =  l_wants_r[ii] &  ~r_o_bp[ii] &  l_wins_r & ~(| l_gets_r[ii-1:0]);
        assign u0_gets_r[ii] = u0_wants_r[ii] &  ~r_o_bp[ii] & u0_wins_r & ~(|u0_gets_r[ii-1:0]);

        assign  r_gets_l[ii] =  r_wants_l[ii] &  ~l_o_bp[ii] &  r_wins_l & ~(| r_gets_l[ii-1:0]);
        assign u0_gets_l[ii] = u0_wants_l[ii] &  ~l_o_bp[ii] & u0_wins_l & ~(|u0_gets_l[ii-1:0]);

        assign l_gets_u0[ii] = l_wants_u0[ii] & ~u0_o_bp[ii] & l_wins_u0 & ~(|l_gets_u0[ii-1:0]);
        assign r_gets_u0[ii] = r_wants_u0[ii] & ~u0_o_bp[ii] & r_wins_u0 & ~(|r_gets_u0[ii-1:0]);
    end : gen_vc_grant
end : gen_static_vc_arb
endgenerate

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Backpressure and Valid Logic
 * --------------------------------------------------------------------------------------------- */

//Valid signals out
//If any VC gets access to a direction, then the data out of that direction is valid
assign l_o_v  = r_gets_l  | u0_gets_l;
assign r_o_v  = l_gets_r  | u0_gets_r;
assign u0_o_v = l_gets_u0 | r_gets_u0;

//Backpressure
generate
for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_vc_bp
    //A particular VC input is backpressured if the most recent packet can't yet go in the direction it wants
    assign  l_i_bp[ii]  = (l_wants_r[ii]  & ~l_gets_r[ii])  | (l_wants_u0[ii] & ~l_gets_u0[ii]);
    assign  r_i_bp[ii]  = (r_wants_l[ii]  & ~r_gets_l[ii])  | (r_wants_u0[ii] & ~r_gets_u0[ii]);
    assign u0_i_bp[ii]  = (u0_wants_l[ii] & ~u0_gets_l[ii]) | (u0_wants_r[ii] & ~u0_gets_r[ii]);
end : gen_vc_bp
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Mux Select Generation Logic
 * --------------------------------------------------------------------------------------------- */

//Left mux
logic [(VC_W*2)-1:0] l_sel_onehot;
assign l_sel_onehot = {r_gets_l, u0_gets_l};
//Parameterized binary encoder
always_comb begin
    l_sel = '0;
    //Priority doesn't matter since we're encoding a one-hot signal
    for (int ii = 0; ii < VC_W*2; ++ii) begin
        if (l_sel_onehot[ii]) begin
            l_sel = ($clog2(VC_W*2))'(ii);
        end
    end
end

//Right mux
logic [(VC_W*2)-1:0] r_sel_onehot;
assign r_sel_onehot = {l_gets_r, u0_gets_r};
always_comb begin
    r_sel = '0;
    for (int ii = 0; ii < VC_W*2; ++ii) begin
        if (r_sel_onehot[ii]) begin
            r_sel = ($clog2(VC_W*2))'(ii);
        end
    end
end

//Up0 mux
logic [(VC_W*2)-1:0] u0_sel_onehot;
assign u0_sel_onehot = {l_gets_u0, r_gets_u0};
always_comb begin
    u0_sel = '0;
    for (int ii = 0; ii < VC_W*2; ++ii) begin
        if (u0_sel_onehot[ii]) begin
            u0_sel = ($clog2(VC_W*2))'(ii);
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//We should never enter an illegal state
assert property (@(posedge clk) disable iff (rst) state != state_e'(2'b11));

//Onehot versions of mux selects should be onehot or 0
assert property (@(posedge clk) disable iff (rst) $onehot0(l_sel_onehot));
assert property (@(posedge clk) disable iff (rst) $onehot0(r_sel_onehot));
assert property (@(posedge clk) disable iff (rst) $onehot0(u0_sel_onehot));

//No two VCs going from and to the same directions should be granted access at the same time
assert property (@(posedge clk) disable iff (rst) $onehot0(l_gets_r));
assert property (@(posedge clk) disable iff (rst) $onehot0(l_gets_u0));
assert property (@(posedge clk) disable iff (rst) $onehot0(r_gets_l));
assert property (@(posedge clk) disable iff (rst) $onehot0(r_gets_u0));
assert property (@(posedge clk) disable iff (rst) $onehot0(u0_gets_l));
assert property (@(posedge clk) disable iff (rst) $onehot0(u0_gets_r));

generate
for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_gets_assertions
    //A given VC should never go in two directions at once
    assert property (@(posedge clk) disable iff (rst) $onehot0({ l_gets_r[ii],  l_gets_u0[ii]}));
    assert property (@(posedge clk) disable iff (rst) $onehot0({ r_gets_l[ii],  r_gets_u0[ii]}));
    assert property (@(posedge clk) disable iff (rst) $onehot0({u0_gets_l[ii], u0_gets_r [ii]}));

    //Nor should it try to go back to itself
    logic l_wants_l, r_wants_r;
    assign l_wants_l = l_i_v[ii] & ~l_i_addr[ii][posl] & (l_i_addr[ii][A_W-1:posl+1] == posx[A_W-posl-2:0]);
    assign r_wants_r = r_i_v[ii] &  r_i_addr[ii][posl] & (r_i_addr[ii][A_W-1:posl+1] == posx[A_W-posl-2:0]);
    assert property (@(posedge clk) disable iff (rst) !l_wants_l);
    assert property (@(posedge clk) disable iff (rst) !r_wants_r);
end : gen_gets_assertions
endgenerate

//Although each input has VC_W fifos, there is only one output datapath per direction
//So the valids should be onehot or 0
assert property (@(posedge clk) disable iff (rst) $onehot0(l_o_v));
assert property (@(posedge clk) disable iff (rst) $onehot0(r_o_v));
assert property (@(posedge clk) disable iff (rst) $onehot0(u0_o_v));

//Control signals should be known out of reset
assert property (@(posedge clk) disable iff (rst) !$isunknown(l_i_v));
assert property (@(posedge clk) disable iff (rst) !$isunknown(r_i_v));
assert property (@(posedge clk) disable iff (rst) !$isunknown(u0_i_v));
assert property (@(posedge clk) disable iff (rst) !$isunknown(l_i_bp));
assert property (@(posedge clk) disable iff (rst) !$isunknown(r_i_bp));
assert property (@(posedge clk) disable iff (rst) !$isunknown(u0_i_bp));
assert property (@(posedge clk) disable iff (rst) !$isunknown(l_o_v));
assert property (@(posedge clk) disable iff (rst) !$isunknown(r_o_v));
assert property (@(posedge clk) disable iff (rst) !$isunknown(u0_o_v));

//Address signals are qualified by the valids
generate
for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_addr_assertions
    assert property (@(posedge clk) disable iff (rst) (| l_i_v[ii] |-> !$isunknown( l_i_addr[ii])));
    assert property (@(posedge clk) disable iff (rst) (| r_i_v[ii] |-> !$isunknown( r_i_addr[ii])));
    assert property (@(posedge clk) disable iff (rst) (|u0_i_v[ii] |-> !$isunknown(u0_i_addr[ii])));
end : gen_addr_assertions
endgenerate

//Select outputs are qualified by the valids
assert property (@(posedge clk) disable iff (rst) (| l_o_v |-> !$isunknown( l_sel)));
assert property (@(posedge clk) disable iff (rst) (| r_o_v |-> !$isunknown( r_sel)));
assert property (@(posedge clk) disable iff (rst) (|u0_o_v |-> !$isunknown(u0_sel)));

initial begin
    //Prevent bad configuration of this module
    assert(A_W == ($clog2(N) + 1));
end

//Useful for manual/automated checking of logs
int now;
always @(posedge clk) begin
    if (now == 0 && posl == 0 && posx == 0) begin
        $display("<credit_t_route>@%0d: Info: N=%0d VC_W=%0d", now, N, VC_W);
    end

    //Minimize the length of lines by cutting this up per VC
    for (int ii = 0; ii < VC_W; ++ii) begin
        if (l_o_v[ii] || r_o_v[ii] || u0_o_v[ii]) begin
            $display(
                "<credit_t_route>@%0d: posl=%0d posx=%0d VC=%0d l_o_v=%0d r_o_v=%0d u0_o_v=%0d l_sel=%0d r_sel=%0d u0_sel=%0d l_i_addr=%0d r_i_addr=%0d u0_i_addr=%0d",
                now,
                posl,
                posx,
                ii,
                l_o_v[ii],
                r_o_v[ii],
                u0_o_v[ii],
                l_sel,
                r_sel,
                u0_sel,
                l_i_addr[ii],
                r_i_addr[ii],
                u0_i_addr[ii]
            );
        end
    end

    now <= now + 1;
end

`endif //SIMULATION

endmodule : credit_t_route
