/**
 * File    t_switch_tb.sv
 * Brief   TODO
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
 * Macros
 * --------------------------------------------------------------------------------------------- */

//Due to Xsim/Verilator mismatches with clocking blocks, we concede defeat and
//have verif live on the negative edge
`define WAITN(n) repeat(n) @(negedge clk)

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module t_switch_tb;

import common_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam N     = DEFAULT_N;   // number of clients
localparam A_W   = DEFAULT_A_W; // log number of clients ($clog2(N) + 1)
localparam D_W   = DEFAULT_D_W;
localparam posl  = 1;           // which level
localparam posx  = 4'b1010;     // which position
localparam VC_W  = DEFAULT_VC_W;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;    // clock
logic rst;    // reset

//Left input
logic [VC_W-1:0][A_W+D_W:0]  l_i;    // left  input
logic [VC_W-1:0]             l_i_bp; // left  input backpressured
logic [VC_W-1:0]             l_i_v;  // left input valid

//Right input
logic [VC_W-1:0][A_W+D_W:0]  r_i;    // right input payload
logic [VC_W-1:0]             r_i_bp; // right input backpressured
logic [VC_W-1:0]             r_i_v;  // right input valid

//Up0 input
logic [VC_W-1:0][A_W+D_W:0]  u0_i;   // u0    input payload
logic [VC_W-1:0]             u0_i_bp;// u0    input backpressured
logic [VC_W-1:0]             u0_i_v; // u0    input valid

//Left output
logic [A_W+D_W:0]    l_o;    // left  output payload
logic [VC_W-1:0]     l_o_bp; // left  output backpressured
logic [VC_W-1:0]     l_o_v;  // left  output valid

//Right output
logic [A_W+D_W:0]    r_o;    // right output payload
logic [VC_W-1:0]     r_o_bp; // right output backpressured
logic [VC_W-1:0]     r_o_v;  // right output valid

//Up0 output
logic [A_W+D_W:0]    u0_o;   // u0    output payload
logic [VC_W-1:0]     u0_o_bp;// u0    output backpressured
logic [VC_W-1:0]     u0_o_v; // u0    output valid

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

t_switch #(
    .N(N),
    .A_W(A_W),
    .D_W(D_W),
    .posl(posl),
    .posx(posx),
    .VC_W(VC_W)
) dut (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

initial begin
    forever begin
        clk = 1'b0;
        #(CLOCK_PERIOD / 2);
        clk = 1'b1;
        #(CLOCK_PERIOD / 2);
    end
end

always @(posedge clk) begin
    $display(
        "t=%t rst=%b l_i_v=%b r_i_v=%b u0_i_v=%b l_i_bp=%b r_i_bp=%b u0_i_bp=%b l_i=%h r_i=%h u0_i=%h l_o_bp=%b r_o_bp=%b u0_o_bp=%b",
        $time, rst,  l_i_v,   r_i_v,   u0_i_v,   l_i_bp,   r_i_bp,   u0_i_bp,   l_i,   r_i,   u0_i,   l_o_bp,   r_o_bp,   u0_o_bp
    );
end

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Assert reset for a couple clock cycles, and set initial inputs
    rst         <= 1'b1;
    l_i_v       <= '0;
    r_i_v       <= '0;
    u0_i_v      <= '0;
    l_i         <= '0;
    r_i         <= '0;
    u0_i        <= '0;
    l_o_bp      <= '0;
    r_o_bp      <= '0;
    u0_o_bp     <= '0;
    `WAITN(2);
    rst <= 1'b0;

    //Simple one-packet-at-a-time tests

    //Routing a packet from the left VC0 to the right VC0 (turning)
    l_i_v  <= 2'b01;
    l_i[0] <= {1'b0, 4'b1010, 32'hABCDABCD};//Top A_W - posl - 1 = 2 bits are the same as posx, and the posl'th bit is set, so this should go to the right
    #(CLOCK_PERIOD / 4);//This will occur combinationaly
    assert(l_i_bp   == '0);//There shouldn't be backpressure since this is the only packet at the moment
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == 2'b01);//The packet should be routed to the right VC0
    assert(u0_o_v   == '0);
    assert(r_o      == {1'b0, 4'b1010, 32'hABCDABCD});
    `WAITN(1);
    r_o_bp <= 2'b01;//Backpressure for a cycle
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b01);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    `WAITN(1);
    l_i_v  <= '0;
    l_i[0] <= '0;
    r_o_bp <= '0;

    //Routing a packet from the right VC1 to the up0 VC1 (ascending)
    r_i_v  <= 2'b10;
    r_i[1] <= {1'b1, 4'b1100, 32'h12344321};//Top A_W - posl - 1 = 2 bits are different from posx, so this should go up
    #(CLOCK_PERIOD / 4);//This will occur combinationaly
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);//There shouldn't be backpressure since this is the only packet at the moment
    assert(u0_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b10);//The packet should be routed to the up0 VC1
    assert(u0_o     == {1'b1, 4'b1100, 32'h12344321});
    `WAITN(1);
    u0_o_bp <= 2'b10;
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == '0);
    assert(r_i_bp   == 2'b10);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    `WAITN(1);
    r_i_v   <= '0;
    r_i[1]  <= '0;
    u0_o_bp <= '0;

    //Routing a packet from the top VC0 to the left VC0 (descending)
    u0_i_v  <= 2'b01;
    u0_i[0] <= {1'b0, 4'b1101, 32'hEFDCBA98};//Bit posl=1 is clear, so this should go to the left
    #(CLOCK_PERIOD / 4);//This will occur combinationaly
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);//There shouldn't be backpressure since this is the only packet at the moment
    assert(l_o_v    == 2'b01);//The packet should be routed to the left VC0
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    assert(l_o      == {1'b0, 4'b1101, 32'hEFDCBA98});
    l_o_bp  <= 2'b10;//Wrong VC backpressured, this should have no effect
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == 2'b01);
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    `WAITN(1);
    u0_i_v  <= '0;
    u0_i[0] <= '0;
    l_o_bp  <= '0;

    //Multiple-packets-at-a-time tests

    //LVC0 -> RVC0, RVC1 -> U0VC1, U0VC0 -> LVC0 all at once
    l_i_v   <= 2'b01;
    l_i[0]  <= {1'b0, 4'b1010, 32'hABCDABCD};
    r_i_v   <= 2'b10;
    r_i[1]  <= {1'b1, 4'b1100, 32'h12344321};
    u0_i_v  <= 2'b01;
    u0_i[0] <= {1'b0, 4'b1101, 32'hEFDCBA98};
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == 2'b01);
    assert(r_o_v    == 2'b01);
    assert(u0_o_v   == 2'b10);
    assert(l_o      == {1'b0, 4'b1101, 32'hEFDCBA98});
    assert(r_o      == {1'b0, 4'b1010, 32'hABCDABCD});
    assert(u0_o     == {1'b1, 4'b1100, 32'h12344321});
    `WAITN(1);
    //Backpressure everything
    l_o_bp       <= '1;
    r_o_bp       <= '1;
    u0_o_bp      <= '1;
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b01);
    assert(r_i_bp   == 2'b10);
    assert(u0_i_bp  == 2'b01);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    `WAITN(1);
    l_i_v   <= '0;
    l_i[0]  <= '0;
    l_o_bp  <= '0;
    r_i_v   <= '0;
    r_i[1]  <= '0;
    r_o_bp  <= '0;
    u0_i_v  <= '0;
    u0_i[0] <= '0;
    u0_o_bp <= '0;

    //Conflict within a direction (both want to ascend)
    l_i_v  <= 2'b11;
    l_i[0] <= {1'b1, 4'b0100, 32'hAAAA5555};
    l_i[1] <= {1'b0, 4'b0100, 32'hBBBB3333};
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b10);//VC1 should be backpressured
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b01);//VC0 is statically prioritized over VC1
    assert(u0_o     == {1'b1, 4'b0100, 32'hAAAA5555});
    `WAITN(1);
    //There should be NO round-robin between VCs in a single direction
    assert(l_i_bp   == 2'b10);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b01);
    assert(u0_o     == {1'b1, 4'b0100, 32'hAAAA5555});
    `WAITN(1);
    u0_o_bp      <= 2'b10;//Backpressure VC1, nothing should change
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b10);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b01);
    assert(u0_o     == {1'b1, 4'b0100, 32'hAAAA5555});
    `WAITN(1);
    u0_o_bp      <= 2'b01;//Backpressure VC0, VC1 should get a turn
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b01);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b10);//Now VC1 gets a turn!
    assert(u0_o     == {1'b0, 4'b0100, 32'hBBBB3333});
    `WAITN(1);
    u0_o_bp      <= 2'b00;//No more backpressure, back to normal
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b10);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b01);
    assert(u0_o     == {1'b1, 4'b0100, 32'hAAAA5555});
    `WAITN(1);
    l_i_v        <= 2'b10;//Now just VC1 is left!
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b00);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b10);//VC1 gets a turn!
    assert(u0_o     == {1'b0, 4'b0100, 32'hBBBB3333});
    `WAITN(1);
    l_i_v  <= '0;
    l_i[0] <= '0;
    l_i[1] <= '0;

    //Conflict between directions (both to RVC1)
    l_i_v   <= 2'b10;
    l_i[1]  <= {1'b0, 4'b1010, 32'h11111111};//Turning to the right
    u0_i_v  <= 2'b10;
    u0_i[1] <= {1'b1, 4'b0010, 32'hEEEEEEEE};//Descending to the right
    #(CLOCK_PERIOD / 4);
    for (int ii = 0; ii < 10; ++ii) begin
        assert(l_i_bp   == '0);
        assert(r_i_bp   == '0);
        assert(u0_i_bp  == 2'b10);//It's L's turn
        assert(l_o_v    == '0);
        assert(r_o_v    == 2'b10);
        assert(u0_o_v   == '0);
        assert(r_o      == {1'b0, 4'b1010, 32'h11111111});
        `WAITN(1);
        assert(l_i_bp   == 2'b10);//It's U0's turn
        assert(r_i_bp   == '0);
        assert(u0_i_bp  == '0);
        assert(l_o_v    == '0);
        assert(r_o_v    == 2'b10);
        assert(u0_o_v   == '0);
        assert(r_o      == {1'b1, 4'b0010, 32'hEEEEEEEE});
        `WAITN(1);
    end
    `WAITN(1);
    r_o_bp      <= 2'b10;//Backpressure VC1, everything should stop
    #(CLOCK_PERIOD / 4);
    for (int ii = 0; ii < 3; ++ii) begin
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == '0);
        assert(u0_i_bp  == 2'b10);
        assert(l_o_v    == '0);
        assert(r_o_v    == '0);
        assert(u0_o_v   == '0);
        `WAITN(1);
    end
    r_o_bp  <= '0;
    l_i_v   <= '0;
    l_i[1]  <= '0;
    u0_i_v  <= '0;
    u0_i[1] <= '0;
    `WAITN(1);//So we end up in the L turn state

    //More tricky tests

    //Conflicts between different directions on different VCs (also all VCs at once)
    l_i_v   <= 2'b11;
    l_i[0]  <= {1'b1, 4'b0101, 32'h00000000};//Ascending
    l_i[1]  <= {1'b0, 4'b0111, 32'h11111111};//Ascending
    r_i_v   <= 2'b11;
    r_i[0]  <= {1'b0, 4'b1000, 32'h22222222};//Going left!
    r_i[1]  <= {1'b1, 4'b0110, 32'h33333333};//Ascending
    u0_i_v  <= 2'b11;
    u0_i[0] <= {1'b1, 4'b1011, 32'h44444444};//Descending to the right
    u0_i[1] <= {1'b1, 4'b1001, 32'h55555555};//Descending to the left
    #(CLOCK_PERIOD / 4);
    for (int ii = 0; ii < 10; ++ii) begin
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == 2'b11);
        assert(u0_i_bp  == 2'b10);
        assert(l_o_v    == 2'b00);//Inefficiently not using the left output this cycle, but this is what the original RTL did so it's fine for now...
        assert(r_o_v    == 2'b01);
        assert(u0_o_v   == 2'b01);
        assert(r_o      == {1'b1, 4'b1011, 32'h44444444});
        assert(u0_o     == {1'b1, 4'b0101, 32'h00000000});
        `WAITN(1);
        assert(l_i_bp   == 2'b11);
        assert(r_i_bp   == 2'b00);
        assert(u0_i_bp  == 2'b10);
        assert(l_o_v    == 2'b01);
        assert(r_o_v    == 2'b01);
        assert(u0_o_v   == 2'b10);
        assert(l_o      == {1'b0, 4'b1000, 32'h22222222});
        assert(r_o      == {1'b1, 4'b1011, 32'h44444444});
        assert(u0_o     == {1'b1, 4'b0110, 32'h33333333});
        `WAITN(1);
        assert(l_i_bp   == 2'b11);
        assert(r_i_bp   == 2'b11);
        assert(u0_i_bp  == 2'b00);
        assert(l_o_v    == 2'b10);
        assert(r_o_v    == 2'b01);
        assert(u0_o_v   == 2'b00);
        assert(l_o      == {1'b1, 4'b1001, 32'h55555555});
        assert(r_o      == {1'b1, 4'b1011, 32'h44444444});
        `WAITN(1);
    end
    u0_o_bp <= 2'b10;//Backpressure U0 VC1
    #(CLOCK_PERIOD / 4);
    for (int ii = 0; ii < 10; ++ii) begin
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == 2'b11);
        assert(u0_i_bp  == 2'b10);
        assert(l_o_v    == 2'b00);
        assert(r_o_v    == 2'b01);
        assert(u0_o_v   == 2'b01);
        assert(r_o      == {1'b1, 4'b1011, 32'h44444444});
        assert(u0_o     == {1'b1, 4'b0101, 32'h00000000});
        `WAITN(1);
        assert(l_i_bp   == 2'b11);
        assert(r_i_bp   == 2'b10);
        assert(u0_i_bp  == 2'b10);
        assert(l_o_v    == 2'b01);
        assert(r_o_v    == 2'b01);
        assert(u0_o_v   == 2'b00);
        assert(l_o      == {1'b0, 4'b1000, 32'h22222222});
        assert(r_o      == {1'b1, 4'b1011, 32'h44444444});
        `WAITN(1);
        assert(l_i_bp   == 2'b11);
        assert(r_i_bp   == 2'b11);
        assert(u0_i_bp  == 2'b00);
        assert(l_o_v    == 2'b10);
        assert(r_o_v    == 2'b01);
        assert(u0_o_v   == 2'b00);
        assert(l_o      == {1'b1, 4'b1001, 32'h55555555});
        assert(r_o      == {1'b1, 4'b1011, 32'h44444444});
        `WAITN(1);
    end
    l_i_v   <= '0;
    l_i[0]  <= '0;
    l_i[1]  <= '0;
    r_i_v   <= '0;
    r_i[0]  <= '0;
    r_i[1]  <= '0;
    u0_i_v  <= '0;
    u0_i[0] <= '0;
    u0_i[1] <= '0;
    u0_o_bp <= '0;
    `WAITN(1);

    //TODO other hard tests (perhaps also with backpressure)

    `WAITN(5);
    $finish;

    //verilator lint_restore
end

endmodule : t_switch_tb
