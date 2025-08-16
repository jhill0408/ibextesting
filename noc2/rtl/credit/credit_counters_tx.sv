/*
 * File:    credit_counters_tx.sv
 * Brief:   Credit counters for transmitter side flow control
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * You can use this if you want lower-level access to the credit counter
 * values (more than credit_counters_tx.sv provides). That can be useful to inform
 * routing decisions for example.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module credit_counters_tx
    import common_pkg::*;
#(
    parameter VC_W  = DEFAULT_VC_W,
    parameter DEPTH = DEFAULT_VC_FIFO_DEPTH//Actual depth is this - 1
) (
    //Clock and reset
    input logic i_clk,
    input logic i_rst,
    
    //Connection to the receiver 
    input   logic [VC_W-1:0]                    i_vc_credit_gnt,

    //Interface for routing logic
    input   logic [VC_W-1:0]                    i_vc_target,    //One valid signal per VC. You musn't assert this if that VC doesn't have a credit!
    output  logic [VC_W-1:0][$clog2(DEPTH)-1:0] o_credits,      //Credit counters per VC
    output  logic [VC_W-1:0][$clog2(DEPTH)-1:0] o_credits_next  //Credit counters per VC for the next cycle
);

/* ------------------------------------------------------------------------------------------------
 * Credit Counters
 * --------------------------------------------------------------------------------------------- */

generate
    for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_vc_logic
        always_comb begin
            if (i_vc_target[ii] & i_vc_credit_gnt[ii]) begin
                //No credit update since we spent and received one on the same cycle
                o_credits_next[ii] = o_credits[ii];
            end else if (i_vc_target[ii]) begin
                o_credits_next[ii] = o_credits[ii] - 1;//Spending a credit
            end else if (i_vc_credit_gnt[ii]) begin
                o_credits_next[ii] = o_credits[ii] + 1;//Receiving a credit
            end else begin
                o_credits_next[ii] = o_credits[ii];//Nothing's happening this cycle
            end
        end

        always_ff @(posedge i_clk) begin
            if (i_rst) begin
                o_credits[ii] <= ($clog2(DEPTH))'(DEPTH - 1);
            end else begin
                o_credits[ii] <= o_credits_next[ii];
            end
        end
    end : gen_vc_logic
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Per VC assertions
generate
for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_vc_assertions
    //Don't go over the max number of credits
    assert property (@(posedge i_clk) disable iff (i_rst) (o_credits[ii]        <= ($clog2(DEPTH))'(DEPTH - 1)));
    assert property (@(posedge i_clk) disable iff (i_rst) (o_credits_next[ii]   <= ($clog2(DEPTH))'(DEPTH - 1)));

    //Don't underflow the credit count
    assert property (@(posedge i_clk) disable iff (i_rst) !(
        (o_credits[ii] == 0) && (i_vc_target[ii] & !i_vc_credit_gnt[ii])
    ));

    //If we're transmitting, that must mean we have at least one credit, else it's bad times
    assert property (@(posedge i_clk) disable iff (i_rst) (i_vc_target[ii] |-> |o_credits[ii]));
end : gen_vc_assertions
endgenerate

//Global assertions

//Control signals should be known out of reset
assert property (@(posedge i_clk) disable iff (i_rst) (!$isunknown(i_vc_credit_gnt)));
assert property (@(posedge i_clk) disable iff (i_rst) (!$isunknown(i_vc_target)));
assert property (@(posedge i_clk) disable iff (i_rst) (!$isunknown(o_credits)));
assert property (@(posedge i_clk) disable iff (i_rst) (!$isunknown(o_credits_next)));

assert property (@(posedge i_clk) disable iff (i_rst) ($onehot0(i_vc_target)));

`endif //SIMULATION

endmodule : credit_counters_tx
