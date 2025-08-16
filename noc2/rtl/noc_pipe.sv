/*
 * File:    noc_pipe.sv
 * Brief:   Configurable-length pipeline to ease timing
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Since the NoC is credit based, additional latency should be invisible!
 * Of course to maintain throughput you likely want to increase the number of
 * max credits if you increase latency...
 *
 * NOTE: We don't want this to optimize down to, for example, SRLC32Es, since
 * the entire purpose of this is to ease timing for distant PEs so the registers
 * that make up the pipeline should be distributed spacially (not in a single slice)
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module noc_pipe
    import common_pkg::*;
#(
    //These should match the parameters of the noc_ifs connected to this module
    parameter int VC_W      = DEFAULT_VC_W,//Number of virtual channels (one bit per VC, not $clog2)
    parameter int A_W       = DEFAULT_A_W,//Address width
    parameter int D_W       = DEFAULT_A_W,//Data width

    //Number of pipeline stages (can be 0 for none at all)
    parameter int LATENCY   = 3
) (
    //Clock and reset
    //Don't have Verilator complain if these aren't used if the latency is 0
    //verilator lint_save
    //verilator lint_off UNUSEDSIGNAL
    input logic         clk,
    input logic         rst,
    //verilator lint_restore

    //Input and output of the pipeline
    noc_if.receiver     from_tx,
    noc_if.transmitter  to_rx
);

/* ------------------------------------------------------------------------------------------------
 * Pipeline
 * --------------------------------------------------------------------------------------------- */

generate
    if (LATENCY == 0) begin : gen_comb_pipe//Purely combinational
        always_comb begin
            //Transmitter -> Receiver
            to_rx.credit_vc_target = from_tx.credit_vc_target;
            to_rx.credit_packet    = from_tx.credit_packet;

            //Receiver -> Transmitter
            from_tx.credit_vc_credit_gnt = to_rx.credit_vc_credit_gnt;
        end
    end : gen_comb_pipe
    else if (LATENCY == 1) begin : gen_single_ff_pipe
        //Only the credit_vc_target and credit_vc_credit_gnt flops need resets
        always_ff @(posedge clk) begin
            if (rst) begin
                to_rx.credit_vc_target         <= '0;
                from_tx.credit_vc_credit_gnt   <= '0;
            end else begin
                to_rx.credit_vc_target         <= from_tx.credit_vc_target;
                from_tx.credit_vc_credit_gnt   <= to_rx.credit_vc_credit_gnt;
            end
        end

        //The others do not, so save some routing cost and gates here
        always_ff @(posedge clk) begin
            //TODO save power by gating flops when the vc signals aren't
            //asserted in the previous stage? There may be an area/perf tradeoff...
            to_rx.credit_packet <= from_tx.credit_packet;
        end
    end : gen_single_ff_pipe
    else begin : gen_multi_ff_pipe//Actual flops, > 1 cycle of latency
        logic [LATENCY-1:0][VC_W-1:0]   credit_vc_target_ffs;
        logic [LATENCY-1:0][VC_W-1:0]   credit_vc_credit_gnt_ffs;
        logic [LATENCY-1:0][A_W+D_W:0]  credit_packet_ffs;

        //Only the credit_vc_target and credit_vc_credit_gnt flops need resets
        always_ff @(posedge clk) begin
            if (rst) begin
                credit_vc_target_ffs[LATENCY-1:0]      <= '0;
                credit_vc_credit_gnt_ffs[LATENCY-1:0]  <= '0;
            end else begin
                credit_vc_target_ffs       <= {credit_vc_target_ffs[LATENCY-2:0], from_tx.credit_vc_target};
                credit_vc_credit_gnt_ffs   <= {credit_vc_credit_gnt_ffs[LATENCY-2:0], to_rx.credit_vc_credit_gnt};
            end
        end

        //The others do not, so save some routing cost and gates here
        always_ff @(posedge clk) begin
            //TODO save power by gating flops when the vc signals aren't
            //asserted in the previous stage? There may be an area/perf tradeoff...
            credit_packet_ffs <= {
                credit_packet_ffs[LATENCY-2:0],
                {from_tx.credit_packet.payload.last, from_tx.credit_packet.routeinfo.addr, from_tx.credit_packet.payload.data}
            };
        end

        //Outputs
        assign to_rx.credit_vc_target              = credit_vc_target_ffs[LATENCY-1];
        assign to_rx.credit_packet.payload.last    = credit_packet_ffs[LATENCY-1][A_W+D_W];
        assign to_rx.credit_packet.routeinfo.addr  = credit_packet_ffs[LATENCY-1][A_W+D_W-1:D_W];
        assign to_rx.credit_packet.payload.data    = credit_packet_ffs[LATENCY-1][D_W-1:0];
        assign from_tx.credit_vc_credit_gnt        = credit_vc_credit_gnt_ffs[LATENCY-1];
    end : gen_multi_ff_pipe
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

//TODO

endmodule : noc_pipe
