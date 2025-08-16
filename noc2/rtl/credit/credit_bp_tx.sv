/*
 * File:    credit_bp_tx.sv
 * Brief:   Credit based backpressure, transmitter side
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * This recieves sends a packet over the noc_if and receives credit info back.
 * It provides a DVR backpressure scheme for the t/pi switch router depending
 * on how many credits it has.
 *
 * This replaces the switch output registers with one half of the credit backpressure mechanism.
 *
 * TODO will need to be invasive and replace the output registers and backpressure logic in t_switch.v
 * and pi_switch.v that are baked in (compared to bp.v which was a separate module)
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module credit_bp_tx
    import common_pkg::*;
#(
    parameter VC_W  = DEFAULT_VC_W,
    parameter D_W   = DEFAULT_D_W,
    parameter A_W   = DEFAULT_A_W,
    parameter DEPTH = DEFAULT_VC_FIFO_DEPTH//Actual depth is this - 1
) (
    //Clock and reset
    input logic clk,
    input logic rst,
    
    //Connection to the receiver 
    noc_if.transmitter to_rx,

    //DVR interface from the switch routing logic
    input   logic [VC_W-1:0]    i_v,//One valid signal per VC
    input   logic [A_W+D_W:0]   i_d,//Data, address, and last signals are per VC; assume the switch has arbitrated this
    output  logic [VC_W-1:0]    o_b //And so too are the backpressure signals
);

logic [VC_W-1:0][$clog2(DEPTH)-1:0] credits;

/* ------------------------------------------------------------------------------------------------
 * Counters Instantiation
 * --------------------------------------------------------------------------------------------- */

credit_counters_tx #(
    .VC_W(VC_W),
    .DEPTH(DEPTH)
) counters_inst (
    //Clock and reset
    .i_clk(clk),
    .i_rst(rst),

    //Connection to the receiver
    .i_vc_credit_gnt(to_rx.credit_vc_credit_gnt),

    //Interface for routing logic
    .i_vc_target(to_rx.credit_vc_target),
    .o_credits(credits),
    //verilator lint_save
    //verilator lint_off PINCONNECTEMPTY
    .o_credits_next()//NU
    //verilator lint_restore
);

/* ------------------------------------------------------------------------------------------------
 * DVR Signal Generation
 * --------------------------------------------------------------------------------------------- */

generate
    for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_vc_logic
        //NOTE: in testing, using o_credits_next instead to do the
        //or-ing/nor-ing before a register actually hurt timing because, in
        //the t switch at least, the critical path is from the FIFO head and
        //tail pointers, through the routing logic, INTO the credit counters (not out of them)
        logic has_credit;
        assign has_credit                   = |credits[ii];
        assign to_rx.credit_vc_target[ii]   = i_v[ii] & has_credit;
        assign o_b[ii]                      = !has_credit;
    end : gen_vc_logic
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Datapath
 * --------------------------------------------------------------------------------------------- */

assign to_rx.credit_packet.payload.data   = i_d[D_W-1:0];
assign to_rx.credit_packet.routeinfo.addr = i_d[A_W+D_W-1:D_W];
assign to_rx.credit_packet.payload.last   = i_d[A_W+D_W];

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Per VC assertions
generate
for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_vc_assertions
    //If we're transmitting, that must mean we have at least one credit, else it's bad times
    assert property (@(posedge clk) disable iff (rst) (to_rx.credit_vc_target[ii] |-> gen_vc_logic[ii].has_credit));

    //Valid shouldn't be deasserted while we are backpressuring if it had already asserted it
    `ifndef VERILATOR//Verilator doesn't support the `throughout` keyword
    //FIXME enable this assertion onces credit_bp_tx_tb has been updated to not accidentally do this
    //Technically this isn't a requirement since this implementation of this module handles this "bad" input fine, but it's a good check to have
    //assert property (@(posedge clk) disable iff (rst) i_v[ii] |-> (i_v[ii] throughout (!o_b[ii])[->1]));
    `endif //VERILATOR
end : gen_vc_assertions
endgenerate

//Global assertions

//Control signals should be known out of reset
assert property (@(posedge clk) disable iff (rst) (!$isunknown(i_v)));
assert property (@(posedge clk) disable iff (rst) (!$isunknown(o_b)));

assert property (@(posedge clk) disable iff (rst) ($onehot0(i_v)));

//Qualified data shouldn't be unknown when valid
assert property (@(posedge clk) disable iff (rst) (|i_v |-> !$isunknown(i_d)));
//(There are already output assertions in noc_if.sv)

`endif //SIMULATION

endmodule : credit_bp_tx
