/*
 * File:    credit_bp_rx.sv
 * Brief:   Credit based backpressure, reciever side
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Based on bp.v
 *
 * This recieves a payload from the noc_if and sends credit info back out
 * It then converts this to a DVR backpressure scheme for the t/pi switch router
 *
 * This replaces the 2:1 mux and shadow register combination with one half
 * of the credit backpressure mechanism
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module credit_bp_rx
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
    
    //Connection to the transmitter
    noc_if.receiver from_tx,

    //DVR interface to the switch routing logic
    output  logic [VC_W-1:0]            o_v,//One valid signal per VC
    output  logic [VC_W-1:0][A_W+D_W:0] o_d,//Data, address, and last signals are per VC
    input   logic [VC_W-1:0]            i_b //And so too are the ready signals
);

generate
    for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_vc_logic
        //Push interface, 1-cycle latency
        logic               push;
        //No need for the `full` signal, since we have credits!
        logic [A_W+D_W:0]   wdata;

        //Pop interface, 1-cycle latency
        logic               pop;
        logic               empty;
        logic [A_W+D_W:0]   rdata;

        //The fifo itself! :)
        fifo32 #(
            .DEPTH32(DEPTH / 32),
            .WIDTH(A_W + D_W + 1),
            .RLATENCY(0)
        ) vc_fifo (
            //Clock and reset
            .clk(clk),
            .rst(rst),

            //Push interface, 1-cycle latency
            .i_push(push),
            //verilator lint_save
            //verilator lint_off PINCONNECTEMPTY
            .o_full(),//NU
            //verilator lint_restore
            .i_wdata(wdata),

            //Pop interface, 1-cycle latency
            .i_pop(pop),
            .o_empty(empty),
            .o_rdata(rdata)
        );

        //Credit logic
        always_comb begin
            push                        = from_tx.vc_target[ii];
            wdata                       = {from_tx.packet.payload.last, from_tx.packet.routeinfo.addr, from_tx.packet.payload.data};
            from_tx.vc_credit_gnt[ii]   = pop;//Whenever we pop, we free up space so we can grant a credit!
        end

        //DVR connections to the switch routing logic
        always_comb begin
            pop     = !i_b[ii] & !empty;
            o_v[ii] = !empty;
            o_d[ii] = rdata;
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
    //Credits should be respected by credit_bp_tx!
    assert property (@(posedge clk) disable iff (rst) !(gen_vc_logic[ii].push && gen_vc_logic[ii].vc_fifo.o_full));

    //We shouldn't pop even without backpressure unless there's actually something to pop
    assert property (@(posedge clk) disable iff (rst) !(gen_vc_logic[ii].empty && gen_vc_logic[ii].pop));

    //Qualified data shouldn't be unknown when valid
    //(There are already input assertions in noc_if.sv)
    assert property (@(posedge clk) disable iff (rst) (o_v[ii] |-> !$isunknown(o_d[ii])));

    //Valid shouldn't be deasserted while we are being backpressured if we have already asserted it
    `ifndef VERILATOR//Verilator doesn't support the `throughout` keyword
    //This implementation should be sufficiently well behaved and shouldn't do this
    assert property (@(posedge clk) disable iff (rst) o_v[ii] |-> (o_v[ii] throughout (!i_b[ii])[->1]));
    `endif //VERILATOR
end : gen_vc_assertions
endgenerate

//Global assertions

//Control signals should be known out of reset
assert property (@(posedge clk) disable iff (rst) (!$isunknown(o_v)));
assert property (@(posedge clk) disable iff (rst) (!$isunknown(i_b)));

`endif //SIMULATION

endmodule : credit_bp_rx
