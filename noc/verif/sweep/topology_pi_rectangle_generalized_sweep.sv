/**
 * File    topology_pi_rectangle_generalized_sweep.sv
 * Brief   TODO
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
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

module topology_pi_rectangle_generalized_sweep;

import common_pkg::*;
import verif_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam N             = `SWEEP_N;
localparam A_W           = $clog2(N) + 1;
localparam D_W           = `SWEEP_D_W;
localparam VC_W          = `SWEEP_VC_W;
localparam VC_FIFO_DEPTH = `SWEEP_VC_FIFO_DEPTH;
localparam GENERALIZED   = 1;

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
    .VC_W(VC_W),
    .D_W(D_W),
    .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
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

logic [N-1:0] client_done;

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

logic [31:0] rate;
logic [31:0] bp_rate;

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
        .rate(rate),
        .sigma(4),
        .done(client_done[ii]),
        .bp_rate(bp_rate),
        //These below should only be changed while rst is high!
        .traffic_type(TRAFFIC_TYPE_SYNTHETIC),
        .synthetic_limit(1000),//Assuming this is being run with Verilator and not dumping waves

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

    //Reset
    rst <= 1'b1;

    //Set rate and bp_rate based on stdin
    assert($value$plusargs("RATE=%d",       rate));
    assert($value$plusargs("BP_RATE=%d",    bp_rate));

    //Leave reset and begin the sim!
    `WAITN(2);
    rst <= 1'b0;

    while (~(|client_done)) begin
        `WAITN(1);
    end

    //Wait a bit longer for in-flight packets to make it out
    `WAITN(1000 * N * rate * (bp_rate + 1));
    $finish;

    //verilator lint_restore
end

endmodule : topology_pi_rectangle_generalized_sweep
