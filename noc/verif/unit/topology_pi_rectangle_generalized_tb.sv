/**
 * File    topology_pi_rectangle_generalized_tb.sv
 * Brief   Rectangular pie
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * "Like pi_simple_4_tb, but MORE"
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

module topology_pi_rectangle_generalized_tb;

import common_pkg::*;
import verif_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam N                = 32;                      // number of clients
localparam INTERFACE_FLOPS  = 1;                       //Number of flops between interfaces, useful to improve timing
localparam A_W              = $clog2(N) + 1;           // log number of clients ($clog2(N) + 1)
localparam D_W              = DEFAULT_D_W;
localparam VC_W             = 8;
localparam VC_FIFO_DEPTH    = DEFAULT_VC_FIFO_DEPTH;   //Actual depth is this - 1
localparam FAIR_VC_ARB      = 0;
localparam GENERALIZED      = 1;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;
logic rst;

//Roots
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) root_rx [N-1:0] (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) root_tx [N-1:0] (
    .*
);

//Leaves
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) leaf_rx [N-1:0] (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) leaf_tx [N-1:0] (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

topology_pi_rectangle #(
    .N(N),
    .INTERFACE_FLOPS(INTERFACE_FLOPS),
    .VC_W(VC_W),
    .D_W(D_W),
    .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
    .FAIR_VC_ARB(FAIR_VC_ARB),
    .GENERALIZED(GENERALIZED)
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

/*

//Working around weird xsim issue where it thinks we have multiple drivers
//even though we don't
logic client0_done, client1_done, client2_done, client3_done;
logic client_done;
assign client_done = client0_done && client1_done && client2_done && client3_done;

always @(posedge clk) begin
    //TODO display other things
    $display("client0_done: %b, client1_done: %b, client2_done: %b, client3_done: %b", client0_done, client1_done, client2_done, client3_done);
end
*/

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

`include "commands.h"

generate
for (genvar ii = 0; ii < N; ++ii) begin : gen_clients
    verif_client #(
        .N(N),
        .D_W(D_W),
        .A_W(A_W),
        .posx(ii),
        .VC_W(VC_W),
        .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
        .TRACE_FNAME(""),
        .MAX_TRACE_LEN(1)
    ) client (
        //Clock and reset
        .clk(clk),
        .rst(rst),

        //Control/status signals
        .synthetic_cmd(SYNTHETIC_CMD_RANDOM),
        .rate(30),
        .sigma(4),
        //.done(client_done),
        .bp_rate(10),
        //These below should only be changed while rst is high!
        //.traffic_type(TRAFFIC_TYPE_SYNTHETIC),
        .traffic_type(TRAFFIC_TYPE_SYNTHETIC),
`ifdef VERILATOR
        .synthetic_limit(100),//Verilator is REALLY fast for long sims
`else
        .synthetic_limit(10),
`endif

        //Connections to the interconnect
        .to_rx(leaf_rx[ii]),
        .from_tx(leaf_tx[ii])
    );
end : gen_clients
endgenerate

//Tie off root signals
generate
for (genvar ii = 0; ii < N; ++ii) begin : gen_root
    assign root_rx[ii].vc_target        = '0;
    assign root_rx[ii].packet           = '0;
    assign root_tx[ii].vc_credit_gnt    = '0;
end : gen_root
endgenerate

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Reset and let it run for a while
    rst <= 1'b1;
    `WAITN(2);
    rst <= 1'b0;

    //The verif_client_check.rs script will ensure correctness
    //of packets sent between the clients
    /*
    while (!client_done) begin
        `WAITN(1);
    end
    */

    //Wait a bit longer for in-flight packets to make it out
`ifdef VERILATOR
    `WAITN(2000);
`else
    `WAITN(200);
`endif
    $finish;

    //verilator lint_restore
end

endmodule : topology_pi_rectangle_generalized_tb
