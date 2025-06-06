/*
 * File:    pi_switch_top.sv
 * Brief:   Switching logic, FIFOs, and credit management
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * To ease timing, it's recommended to place a noc_pipe between this switch's
 * output and the destination, if the desitnation is not physically close
 * or lacks input buffering.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module pi_switch_top
    import common_pkg::*;
#(
    parameter N             = DEFAULT_N,            // number of clients
    parameter A_W           = DEFAULT_A_W,          // log number of clients ($clog2(N) + 1)
    parameter D_W           = DEFAULT_D_W,
    parameter posl          = 0,                    // Vertical position in the NoC
    parameter posx          = 0,                    // Horizontal position in the level
    parameter VC_W          = DEFAULT_VC_W,
    parameter VC_FIFO_DEPTH = DEFAULT_VC_FIFO_DEPTH,//Actual depth is this - 1
    parameter FAIR_VC_ARB   = 0,                    //Whether to use static VC prioritization or matrix arbiters
    parameter GENERALIZED   = 0                     // Set to 1 to enable generalized upwards routing based on the address
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

/* ------------------------------------------------------------------------------------------------
 * Input Backpressure (Credit I/F -> DVR I/F)
 * --------------------------------------------------------------------------------------------- */

//DVR interface to the switch routing logic
logic [VC_W-1:0]            l_i_v, r_i_v, u0_i_v, u1_i_v;//Is the input data valid? (from the fifos)
logic [VC_W-1:0][A_W+D_W:0] l_i_d, r_i_d, u0_i_d, u1_i_d;//Data from the fifos
logic [VC_W-1:0]            l_i_b, r_i_b, u0_i_b, u1_i_b;//Are the fifos backpressured? (from us to the fifos)

credit_bp_rx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(VC_FIFO_DEPTH)
) l_rx_fifos (
    //Clock and reset
    .clk(clk),
    .rst(rst),

    //Connection to the transmitter
    .from_tx(l_rx),

    //DVR interface to the switch routing logic
    .o_v(l_i_v),
    .o_d(l_i_d),
    .i_b(l_i_b)
);

credit_bp_rx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(VC_FIFO_DEPTH)
) r_rx_fifos (
    //Clock and reset
    .clk(clk),
    .rst(rst),

    //Connection to the transmitter
    .from_tx(r_rx),

    //DVR interface to the switch routing logic
    .o_v(r_i_v),
    .o_d(r_i_d),
    .i_b(r_i_b)
);

credit_bp_rx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(VC_FIFO_DEPTH)
) u0_rx_fifos (
    //Clock and reset
    .clk(clk),
    .rst(rst),

    //Connection to the transmitter
    .from_tx(u0_rx),

    //DVR interface to the switch routing logic
    .o_v(u0_i_v),
    .o_d(u0_i_d),
    .i_b(u0_i_b)
);

credit_bp_rx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(VC_FIFO_DEPTH)
) u1_rx_fifos (
    //Clock and reset
    .clk(clk),
    .rst(rst),

    //Connection to the transmitter
    .from_tx(u1_rx),

    //DVR interface to the switch routing logic
    .o_v(u1_i_v),
    .o_d(u1_i_d),
    .i_b(u1_i_b)
);

/* ------------------------------------------------------------------------------------------------
 * Switching Logic
 * --------------------------------------------------------------------------------------------- */

logic [VC_W-1:0]    l_o_v, r_o_v, u0_o_v, u1_o_v;//Is the input data valid? (from the switch)
logic [A_W+D_W:0]   l_o_d, r_o_d, u0_o_d, u1_o_d;//Data from the switch
logic [VC_W-1:0]    l_o_b, r_o_b, u0_o_b, u1_o_b;//Are we backpressured? (from the credit counters)

pi_switch #(
    .N          (N),    
    .A_W        (A_W),
    .D_W        (D_W),
    .posl       (posl),
    .posx       (posx),
    .VC_W       (VC_W),
    .FAIR_VC_ARB(FAIR_VC_ARB),
    .GENERALIZED(GENERALIZED)
) pi_switch_inst (
    //Clock and reset
    .clk        (clk),      // clock
    .rst        (rst),      // reset

    //Left input
    .l_i        (l_i_d),    // left  input payload
    .l_i_bp     (l_i_b),    // left  input backpressured
    .l_i_v      (l_i_v),    // left  input valid

    //Right input
    .r_i        (r_i_d),    // right input payload
    .r_i_bp     (r_i_b),    // right input backpressured
    .r_i_v      (r_i_v),    // right input valid

    //Up0 input
    .u0_i       (u0_i_d),   // u0    input payload
    .u0_i_bp    (u0_i_b),   // u0    input backpressured
    .u0_i_v     (u0_i_v),   // u0    input valid

    //Up1 input
    .u1_i       (u1_i_d),   // u1    input payload
    .u1_i_bp    (u1_i_b),   // u1    input backpressured
    .u1_i_v     (u1_i_v),   // u1    input valid

    //Left output
    .l_o        (l_o_d),    // left  output payload
    .l_o_bp     (l_o_b),    // left  output backpressured
    .l_o_v      (l_o_v),    // left  output valid

    //Right output
    .r_o        (r_o_d),    // right output payload
    .r_o_bp     (r_o_b),    // right output backpressured
    .r_o_v      (r_o_v),    // right output valid
    
    //Up0 output
    .u0_o       (u0_o_d),   // u0    output payload
    .u0_o_bp    (u0_o_b),   // u0    output backpressured
    .u0_o_v     (u0_o_v),   // u0    output valid
    
    //Up1 output
    .u1_o       (u1_o_d),   // u1    output payload
    .u1_o_bp    (u1_o_b),   // u1    output backpressured
    .u1_o_v     (u1_o_v)    // u1    output valid
);

/* ------------------------------------------------------------------------------------------------
 * Output Backpressure (DVR I/F -> Credit I/F)
 * --------------------------------------------------------------------------------------------- */

credit_bp_tx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(VC_FIFO_DEPTH)
) l_tx_credit_counters (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Connection to the receiver 
    .to_rx(l_tx),

    //DVR interface from the switch routing logic
    .i_v(l_o_v),
    .i_d(l_o_d),
    .o_b(l_o_b)
);

credit_bp_tx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(VC_FIFO_DEPTH)
) r_tx_credit_counters (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Connection to the receiver 
    .to_rx(r_tx),

    //DVR interface from the switch routing logic
    .i_v(r_o_v),
    .i_d(r_o_d),
    .o_b(r_o_b)
);

credit_bp_tx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(VC_FIFO_DEPTH)
) u0_tx_credit_counters (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Connection to the receiver 
    .to_rx(u0_tx),

    //DVR interface from the switch routing logic
    .i_v(u0_o_v),
    .i_d(u0_o_d),
    .o_b(u0_o_b)
);

credit_bp_tx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(VC_FIFO_DEPTH)
) u1_tx_credit_counters (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Connection to the receiver 
    .to_rx(u1_tx),

    //DVR interface from the switch routing logic
    .i_v(u1_o_v),
    .i_d(u1_o_d),
    .o_b(u1_o_b)
);

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

`endif //SIMULATION

endmodule : pi_switch_top
