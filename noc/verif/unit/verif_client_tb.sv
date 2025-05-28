/**
 * File    verif_client_tb.sv
 * Brief   Testbench for verif_client
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

module verif_client_tb;

import common_pkg::*;
import verif_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam N             = 2;                                             // total number of clients
localparam D_W           = DEFAULT_D_W;                                   // data width
localparam A_W           = DEFAULT_A_W;                                   // address width
localparam posx          = 0;                                             // position
localparam VC_W          = DEFAULT_VC_W;                                  // Number of virtual channels (one bit per VC, not $clog2)
localparam VC_FIFO_DEPTH = DEFAULT_VC_FIFO_DEPTH;                         // Actual depth is this - 1
localparam TRACE_FNAME   = `"`REPO_ROOT/trace/sanity0/1/autogen_0.trace`";// Initially loaded trace; use the load_trace() function to change dynamically
localparam MAX_TRACE_LEN = 100;                                           // Max number of entries in the trace files

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;
logic rst = 1'b1;//To ensure rst is asserted at the beginning of the sim

//Control/status signals
synthetic_cmd_e synthetic_cmd;//Only considered if traffic_type is TRAFFIC_TYPE_SYNTHETIC
logic [31:0]    rate;           // rate of injection (in percent) 
logic [31:0]    sigma;          // radius for LOCAL traffic
logic           done;
logic [31:0]    bp_rate;        // rate of backpressuring (in percent)
//These below should only be changed while rst is high!
traffic_type_e  traffic_type;
logic [31:0]    synthetic_limit;// When to stop injecting packets (for the synthetic traffic type)

//Connections to the interconnect
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) to_rx (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) from_tx (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

verif_client #(
    .N(N),
    .D_W(D_W),
    .A_W(A_W),
    .posx(posx),
    .VC_W(VC_W),
    .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
    .TRACE_FNAME(TRACE_FNAME),
    .MAX_TRACE_LEN(MAX_TRACE_LEN)
) dut (
    .*
);

logic rx_helper_done;
verif_client #(
    .N(N),
    .D_W(D_W),
    .A_W(A_W),
    .posx(1),
    .VC_W(VC_W),
    .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
    .TRACE_FNAME(TRACE_FNAME),
    .MAX_TRACE_LEN(MAX_TRACE_LEN)
) rx_helper (//Only receives
    //Clock and reset
    .clk(clk),
    .rst(rst),
    
    //Control/status signals
    .synthetic_cmd(SYNTHETIC_CMD_DONT_CARE),
    .rate('0),
    .sigma('0),
    .done(rx_helper_done),
    .bp_rate(10),//10% should be good :)
    //These below should only be changed while rst is high!
    .traffic_type(TRAFFIC_TYPE_RX_ONLY),
    .synthetic_limit('0),

    //Connections to the interconnect
    //Reversed compared to `dut`
    .to_rx(from_tx),
    .from_tx(to_rx)
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

always @(posedge clk) begin
    $display(
        "t=%t rst=%b vc_target=%b packet={%h,%h,%h} vc_credit_gnt=%b done=%b rx_helper_done=%b",
        $time, rst,  to_rx.vc_target,
        to_rx.packet.payload.data, to_rx.packet.payload.last, to_rx.packet.routeinfo.addr,
        to_rx.vc_credit_gnt,
        done, rx_helper_done
    );
end

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    bp_rate <= 32'd0;//Don't backpressure since this DUT never recieves in this testbench

    //Reset things and try out synthetic traffic generation
    rst                 <= 1'b1;
    from_tx.vc_target   <= '0;
    to_rx.vc_credit_gnt <= '0;
    synthetic_cmd       <= SYNTHETIC_CMD_RANDOM;
    rate                <= 32'd30;//30% rate
    sigma               <= 32'd0;
    traffic_type        <= TRAFFIC_TYPE_SYNTHETIC;//Start out with a synthetic test :)
    synthetic_limit     <= 32'd10;//Limit to 10 attempts
    `WAITN(2);
    rst                 <= 1'b0;
    `WAITN(500);

    //TODO try other synthetic_cmd types

    //Now try out the TRACE_FNAME trace
    rst                 <= 1'b1;
    from_tx.vc_target   <= '0;
    to_rx.vc_credit_gnt <= '0;
    synthetic_cmd       <= SYNTHETIC_CMD_DONT_CARE;
    rate                <= 32'd30;//30% rate
    sigma               <= '0;
    traffic_type        <= TRAFFIC_TYPE_TRACE;//Will use TRACE_FNAME since we haven't called load_trace()
    synthetic_limit     <= '0;
    `WAITN(2);
    rst                 <= 1'b0;
    `WAITN(500);

    //Lastly, load a different trace
    rst                 <= 1'b1;
    from_tx.vc_target   <= '0;
    to_rx.vc_credit_gnt <= '0;
    synthetic_cmd       <= SYNTHETIC_CMD_DONT_CARE;
    rate                <= 32'd30;//30% rate
    sigma               <= '0;
    traffic_type        <= TRAFFIC_TYPE_TRACE;//Will use TRACE_FNAME since we haven't called load_trace()
    synthetic_limit     <= '0;
    `WAITN(2);
    dut.load_trace(`"`REPO_ROOT/trace/sanity1/1/autogen_0.trace`");
    `WAITN(2);
    rst                 <= 1'b0;
    `WAITN(500);

    //Do another, this time bigger synthetic run
    rst                 <= 1'b1;
    from_tx.vc_target   <= '0;
    to_rx.vc_credit_gnt <= '0;
    synthetic_cmd       <= SYNTHETIC_CMD_RANDOM;
    rate                <= 32'd30;//30% rate
    sigma               <= 32'd0;
    traffic_type        <= TRAFFIC_TYPE_SYNTHETIC;//Start out with a synthetic test :)
    synthetic_limit     <= 32'd100;//Limit to 100 attempts
    `WAITN(2);
    rst                 <= 1'b0;
    `WAITN(500);

    $finish;

    //verilator lint_restore
end

endmodule : verif_client_tb
