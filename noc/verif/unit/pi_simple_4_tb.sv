/**
 * File    pi_simple_4_tb.sv
 * Brief   First multi-pi-switch test!
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * L2
 * L1          π               π
 *            / \       /-----/ \
 *           |   \-----/-----\   |
 *            \ /-----/       \ /
 * L0          π               π
 *            / \             / \
 *            C C             C C
 *
 * X:          0               1
 * X:         0 1             2 3
 *
 * (I'm not an artist. Also this is a bit inaccurate as the right top switch
 * is kinda also X=0 since it can access the same children as the left top one.
 * But the fancy ASCII wires are pretty bang on!)
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

module pi_simple_4_tb;

import common_pkg::*;
import verif_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam N             = 4;                       // number of clients
localparam A_W           = 3;                       // log number of clients ($clog2(N) + 1)
localparam D_W           = DEFAULT_D_W;
localparam VC_W          = 4;
localparam VC_FIFO_DEPTH = DEFAULT_VC_FIFO_DEPTH;   //Actual depth is this - 1

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;    // clock
logic rst;    // reset

//Root

//Level 2
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l2a_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l2a_up_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l2b_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l2b_up_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l2c_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l2c_up_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l2d_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l2d_up_if (
    .*
);

//Level 1
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l1a_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l1a_up_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l1b_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l1b_up_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l1c_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l1c_up_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l1d_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l1d_up_if (
    .*
);

//Level 0
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l0a_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l0a_up_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l0b_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l0b_up_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l0c_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l0c_up_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l0d_down_if (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l0d_up_if (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * DUTs
 * --------------------------------------------------------------------------------------------- */

//Level 1
pi_switch_top #(
    .N(N),
    .A_W(A_W),
    .D_W(D_W),
    .posl(1),
    .posx(0),
    .VC_W(VC_W)
) l1x0 (
    .*,
    .l_rx(l1a_up_if),
    .r_rx(l1c_up_if),
    .u0_rx(l2a_down_if),
    .u1_rx(l2c_down_if),
    .l_tx(l1a_down_if),
    .r_tx(l1c_down_if),
    .u0_tx(l2a_up_if),
    .u1_tx(l2c_up_if)
);

pi_switch_top #(
    .N(N),
    .A_W(A_W),
    .D_W(D_W),
    .posl(1),
    .posx(0),//Note this is ACTUALLY 0 since both this and l1x0 can access either l0 pi switch
    .VC_W(VC_W)
) l1x1 (//A bit of a misnomer, but this works!
    .*,
    .l_rx(l1b_up_if),
    .r_rx(l1d_up_if),
    .u0_rx(l2b_down_if),
    .u1_rx(l2d_down_if),
    .l_tx(l1b_down_if),
    .r_tx(l1d_down_if),
    .u0_tx(l2b_up_if),
    .u1_tx(l2d_up_if)
);

//Level 0
pi_switch_top #(
    .N(N),
    .A_W(A_W),
    .D_W(D_W),
    .posl(0),
    .posx(0),
    .VC_W(VC_W)
) l0x0 (
    .*,
    .l_rx(l0a_up_if),
    .r_rx(l0b_up_if),
    .u0_rx(l1a_down_if),
    .u1_rx(l1b_down_if),
    .l_tx(l0a_down_if),
    .r_tx(l0b_down_if),
    .u0_tx(l1a_up_if),
    .u1_tx(l1b_up_if)
);

pi_switch_top #(
    .N(N),
    .A_W(A_W),
    .D_W(D_W),
    .posl(0),
    .posx(1),
    .VC_W(VC_W)
) l0x1 (
    .*,
    .l_rx(l0c_up_if),
    .r_rx(l0d_up_if),
    .u0_rx(l1c_down_if),
    .u1_rx(l1d_down_if),
    .l_tx(l0c_down_if),
    .r_tx(l0d_down_if),
    .u0_tx(l1c_up_if),
    .u1_tx(l1d_up_if)
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

//Working around weird xsim issue where it thinks we have multiple drivers
//even though we don't
logic client0_done, client1_done, client2_done, client3_done;
logic client_done;
assign client_done = client0_done && client1_done && client2_done && client3_done;

always @(posedge clk) begin
    //TODO display other things
    $display("client0_done: %b, client1_done: %b, client2_done: %b, client3_done: %b", client0_done, client1_done, client2_done, client3_done);
end

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

`include "commands.h"

verif_client #(
    .N(N),
    .D_W(D_W),
    .A_W(A_W),
    .posx(0),
    .VC_W(VC_W),
    .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
    .TRACE_FNAME(""),
    .MAX_TRACE_LEN(1)
) client0 (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Control/status signals
    .synthetic_cmd(SYNTHETIC_CMD_RANDOM),
    .rate(30),
    .sigma(4),
    .done(client0_done),
    .bp_rate(10),
    //These below should only be changed while rst is high!
    .traffic_type(TRAFFIC_TYPE_SYNTHETIC),
    .synthetic_limit(1000),// When to stop injecting packets (for the synthetic traffic type)

    //Connections to the interconnect
    .to_rx(l0a_up_if),
    .from_tx(l0a_down_if)
);

verif_client #(
    .N(N),
    .D_W(D_W),
    .A_W(A_W),
    .posx(1),
    .VC_W(VC_W),
    .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
    .TRACE_FNAME(""),
    .MAX_TRACE_LEN(1)
) client1 (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Control/status signals
    .synthetic_cmd(SYNTHETIC_CMD_RANDOM),
    .rate(30),
    .sigma(4),
    .done(client1_done),
    .bp_rate(10),
    //These below should only be changed while rst is high!
    .traffic_type(TRAFFIC_TYPE_SYNTHETIC),
    .synthetic_limit(1000),// When to stop injecting packets (for the synthetic traffic type)

    //Connections to the interconnect
    .to_rx(l0b_up_if),
    .from_tx(l0b_down_if)
);

verif_client #(
    .N(N),
    .D_W(D_W),
    .A_W(A_W),
    .posx(2),
    .VC_W(VC_W),
    .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
    .TRACE_FNAME(""),
    .MAX_TRACE_LEN(1)
) client2 (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Control/status signals
    .synthetic_cmd(SYNTHETIC_CMD_RANDOM),
    .rate(30),
    .sigma(4),
    .done(client2_done),
    .bp_rate(10),
    //These below should only be changed while rst is high!
    .traffic_type(TRAFFIC_TYPE_SYNTHETIC),
    .synthetic_limit(1000),// When to stop injecting packets (for the synthetic traffic type)

    //Connections to the interconnect
    .to_rx(l0c_up_if),
    .from_tx(l0c_down_if)
);

verif_client #(
    .N(N),
    .D_W(D_W),
    .A_W(A_W),
    .posx(3),
    .VC_W(VC_W),
    .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
    .TRACE_FNAME(""),
    .MAX_TRACE_LEN(1)
) client3 (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Control/status signals
    .synthetic_cmd(SYNTHETIC_CMD_RANDOM),
    .rate(30),
    .sigma(4),
    .done(client3_done),
    .bp_rate(10),
    //These below should only be changed while rst is high!
    .traffic_type(TRAFFIC_TYPE_SYNTHETIC),
    .synthetic_limit(1000),// When to stop injecting packets (for the synthetic traffic type)

    //Connections to the interconnect
    .to_rx(l0d_up_if),
    .from_tx(l0d_down_if)
);

//Tie off root signals
assign l2a_down_if.vc_target   = '0;
assign l2a_down_if.packet      = '0;
assign l2a_up_if.vc_credit_gnt = '0;
assign l2b_down_if.vc_target   = '0;
assign l2b_down_if.packet      = '0;
assign l2b_up_if.vc_credit_gnt = '0;
assign l2c_down_if.vc_target   = '0;
assign l2c_down_if.packet      = '0;
assign l2c_up_if.vc_credit_gnt = '0;
assign l2d_down_if.vc_target   = '0;
assign l2d_down_if.packet      = '0;
assign l2d_up_if.vc_credit_gnt = '0;

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Reset and let it run for a while
    rst <= 1'b1;
    `WAITN(2);
    rst <= 1'b0;

    //The verif_client_check.rs script will ensure correctness
    //of packets sent between the clients
    while (!client_done) begin
        `WAITN(1);
    end

    //Wait a bit longer for in-flight packets to make it out
    `WAITN(1000);
    $finish;

    //verilator lint_restore
end

endmodule : pi_simple_4_tb
