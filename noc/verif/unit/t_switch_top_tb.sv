/**
 * File    t_switch_top_tb.sv
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

module t_switch_top_tb;

import common_pkg::*;
import verif_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam N             = 2;                       // number of clients
localparam A_W           = $clog2(N) + 1;           // log number of clients ($clog2(N) + 1)
localparam D_W           = DEFAULT_D_W;
localparam posl          = 0;                       // which level
localparam posx          = 0;                       // which position
localparam VC_W          = DEFAULT_VC_W;
localparam VC_FIFO_DEPTH = DEFAULT_VC_FIFO_DEPTH;   //Actual depth is this - 1

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;    // clock
logic rst;    // reset

//Switch datapath inputs
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l_rx (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) r_rx (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) u0_rx (
    .*
);

//Switch datapath outputs
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) l_tx (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) r_tx (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) u0_tx (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

t_switch_top #(
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

logic l_done, r_done;

always @(posedge clk) begin
    //TODO display other things
    $display("l_done = %b, r_done = %b", l_done, r_done);
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
) l_client (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Control/status signals
    .synthetic_cmd(SYNTHETIC_CMD_RANDOM),
    .rate(30),
    .sigma(4),
    .done(l_done),
    .bp_rate(10),
    //These below should only be changed while rst is high!
    .traffic_type(TRAFFIC_TYPE_SYNTHETIC),
    .synthetic_limit(1000),// When to stop injecting packets (for the synthetic traffic type)

    //Connections to the interconnect
    .to_rx(l_rx),
    .from_tx(l_tx)
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
) r_client (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Control/status signals
    .synthetic_cmd(SYNTHETIC_CMD_RANDOM),
    .rate(30),
    .sigma(4),
    .done(r_done),
    .bp_rate(10),
    //These below should only be changed while rst is high!
    .traffic_type(TRAFFIC_TYPE_SYNTHETIC),
    .synthetic_limit(1000),// When to stop injecting packets (for the synthetic traffic type)

    //Connections to the interconnect
    .to_rx(r_rx),
    .from_tx(r_tx)
);

//Tie off upper signals since we only have two clients
assign u0_rx.vc_target      = '0;
assign u0_rx.packet         = '0;
assign u0_tx.vc_credit_gnt  = '0;

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Reset and let it run for a while
    rst <= 1'b1;
    `WAITN(2);
    rst <= 1'b0;

    //The verif_client_check.rs script will ensure correctness
    //of packets sent between the clients
    while (!l_done && !r_done) begin
        `WAITN(1);
    end

    //Wait a bit longer for in-flight packets to make it out
    `WAITN(1000);
    $finish;

    //verilator lint_restore
end

endmodule : t_switch_top_tb
