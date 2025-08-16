/*
 * File:    pi_switch_top.sv
 * Brief:   TODO
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * TODO
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module pi_switch_top
    import common_pkg::*;
#(
    parameter bft_type_e    BFT_TYPE      = BFT_TYPE_CREDITS,
    parameter int           N             = DEFAULT_N,            // number of clients
    parameter int           A_W           = DEFAULT_A_W,          // log number of clients ($clog2(N) + 1)
    parameter int           D_W           = DEFAULT_D_W,
    parameter int           posl          = 0,                    // Vertical position in the NoC
    parameter int           posx          = 0,                    // Horizontal position in the level
    parameter int           VC_W          = DEFAULT_VC_W,
    parameter int           VC_FIFO_DEPTH = DEFAULT_VC_FIFO_DEPTH,//Actual depth is this - 1
    parameter int           FAIR_VC_ARB   = 0,                    //Whether to use static VC prioritization or matrix arbiters
    parameter int           GENERALIZED   = 0                     // Set to 1 to enable generalized upwards routing based on the address
) (
    //Clock and reset
    input  logic clk,// clock
    input  logic rst,// reset
    
    //Switch datapath inputs
    noc_if.receiver     l_rx,
    noc_if.receiver     r_rx,
    noc_if.receiver     u0_rx,
    noc_if.receiver     u1_rx,

    //Switch datapath outputs
    noc_if.transmitter  l_tx,
    noc_if.transmitter  r_tx,
    noc_if.transmitter  u0_tx,
    noc_if.transmitter  u1_tx
);

generate
if (BFT_TYPE == BFT_TYPE_CREDITS) begin : gen_credit_pi
    credit_pi_switch_top #(
        .N(N),
        .A_W(A_W),
        .D_W(D_W),
        .posl(posl),
        .posx(posx),
        .VC_W(VC_W),
        .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
        .FAIR_VC_ARB(FAIR_VC_ARB),
        .GENERALIZED(GENERALIZED)
    ) pi_switch (
        .*
    );
end : gen_credit_pi
else if (BFT_TYPE == BFT_TYPE_BACKPRESSURE) begin : gen_bp_pi
    //TODO
end : gen_bp_pi
else if (BFT_TYPE == BFT_TYPE_DEFLECTION) begin : gen_deflection_pi
    //TODO
end : gen_deflection_pi
endgenerate

endmodule : pi_switch_top
