/**
 * File    noc_pipe_tb.sv
 * Brief   Testbench for noc_pipe
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Includes
 * --------------------------------------------------------------------------------------------- */

`include "commands.h"

/* ------------------------------------------------------------------------------------------------
 * Macros
 * --------------------------------------------------------------------------------------------- */

//Due to Xsim/Verilator mismatches with clocking blocks, we concede defeat and
//have verif live on the negative edge
`define WAITN(n) repeat(n) @(negedge clk)

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module noc_pipe_tb;

import common_pkg::*;
import verif_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

parameter int N         = 2;

//These should match the parameters of the noc_ifs connected to this module
parameter int VC_W      = DEFAULT_VC_W;//Number of virtual channels (one bit per VC, not $clog2)
parameter int A_W       = $clog2(N) + 1;//Address width
parameter int D_W       = DEFAULT_D_W;//Data width

//Number of pipeline stages (can be 0 for none at all)
parameter int LATENCY   = 10;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;
logic rst = 1'b1;//To ensure rst is asserted at the beginning of the sim

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W),
    .D_W(D_W)
) a_out (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W),
    .D_W(D_W)
) a_in (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W),
    .D_W(D_W)
) b_out (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W),
    .D_W(D_W)
) b_in (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * DUTs
 * --------------------------------------------------------------------------------------------- */

noc_pipe #(
    .VC_W(VC_W),
    .A_W(A_W),
    .D_W(D_W),
    .LATENCY(LATENCY)
) dut_a2b (
    .clk(clk),
    .rst(rst),
    .from_tx(a_out),
    .to_rx(b_in)
);

noc_pipe #(
    .VC_W(VC_W),
    .A_W(A_W),
    .D_W(D_W),
    .LATENCY(LATENCY)
) dut_b2a (
    .clk(clk),
    .rst(rst),
    .from_tx(b_out),
    .to_rx(a_in)
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

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

logic a_done;
logic b_done;

verif_client #(
    .N(N),
    .A_W(A_W),
    .D_W(D_W),
    .posx(0),
    .VC_W(VC_W)
) client_a (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Control/status signals
    .synthetic_cmd(SYNTHETIC_CMD_RANDOM),
    .rate(30),
    .sigma('0),
    .done(a_done),
    .bp_rate(10),//10% should be good :)
    //These below should only be changed while rst is high!
    .traffic_type(TRAFFIC_TYPE_SYNTHETIC),
    .synthetic_limit(1000),

    //Connections to the interconnect
    .to_rx(a_out),
    .from_tx(a_in)
);

verif_client #(
    .N(N),
    .A_W(A_W),
    .D_W(D_W),
    .posx(1),
    .VC_W(VC_W)
) client_b (
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Control/status signals
    .synthetic_cmd(SYNTHETIC_CMD_RANDOM),
    .rate(30),
    .sigma('0),
    .done(b_done),
    .bp_rate(10),//10% should be good :)
    //These below should only be changed while rst is high!
    .traffic_type(TRAFFIC_TYPE_SYNTHETIC),
    .synthetic_limit(1000),

    //Connections to the interconnect
    .to_rx(b_out),
    .from_tx(b_in)
);

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Reset and let it run for a while
    rst <= 1'b1;
    `WAITN(2);
    rst <= 1'b0;

    //The verif_client_check.rs script will ensure correctness
    //of packets sent between the clients
    while (!a_done || !b_done) begin
        `WAITN(1);
    end

    //Wait a bit longer for in-flight packets to make it out
    `WAITN(1000);
    $finish;

    //verilator lint_restore
end

endmodule : noc_pipe_tb
