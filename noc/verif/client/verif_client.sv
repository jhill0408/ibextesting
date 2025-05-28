/*
 * File:    verif_client.sv
 * Brief:   Sends and receives packets for testing purposes
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * NOT SYNTHESIZABLE
 * Has credit interfaces and is VC aware! :)
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module verif_client
    import common_pkg::*;
    import verif_pkg::*;
#(
    parameter N             = DEFAULT_N,            // total number of clients
    parameter D_W           = DEFAULT_D_W,          // data width
    parameter A_W           = DEFAULT_A_W,          // address width
    parameter posx          = 2,                    // position
    parameter VC_W          = DEFAULT_VC_W,         // Number of virtual channels (one bit per VC, not $clog2)
    parameter VC_FIFO_DEPTH = DEFAULT_VC_FIFO_DEPTH,// Actual depth is this - 1
    parameter TRACE_FNAME   = "",                   // Initially loaded trace; use the load_trace() function to change dynamically
    parameter MAX_TRACE_LEN = 1                     // Max number of entries in the trace files
) (
    //Clock and reset
    input logic clk,
    input logic rst,

    //Control/status signals
    input  synthetic_cmd_e  synthetic_cmd,//Only considered if traffic_type is TRAFFIC_TYPE_SYNTHETIC
    input  logic [31:0]     rate,           // rate of injection (in percent) 
    input  logic [31:0]     sigma,          // radius for LOCAL traffic
    output logic            done,
    input  logic [31:0]     bp_rate,        // rate of backpressuring (in percent) //TODO possibly add support for backpressuring different VCs at different rates?
    //These below should only be changed while rst is high!
    input  traffic_type_e   traffic_type,
    input  logic [31:0]     synthetic_limit,// When to stop injecting packets (for the synthetic traffic type)

    //Connections to the interconnect
    //TODO or should this be AXI-S and we use an axi_bridge instance?
    //Nah, actually if anything we could provide an axi_bridge module and just
    //use it internally in here later (perhaps even base it off of this)
    noc_if.transmitter  to_rx,
    noc_if.receiver     from_tx
);

/* ------------------------------------------------------------------------------------------------
 * DVR <-> Credit Logic
 * --------------------------------------------------------------------------------------------- */

logic [VC_W-1:0]  o_v;
logic [VC_W-1:0]  o_bp;
logic [A_W+D_W:0] o_d;

logic [VC_W-1:0]            i_v;
logic [VC_W-1:0]            i_bp;
logic [VC_W-1:0][A_W+D_W:0] i_d;

credit_bp_tx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(VC_FIFO_DEPTH)
) tx_counters (
    //Clock and reset
    .clk(clk),
    .rst(rst),

    //Connection to the receiver
    .to_rx(to_rx),

    //DVR interface from the switch routing logic
    .i_v(o_v),
    .i_d(o_d),
    .o_b(o_bp)
);

credit_bp_rx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(VC_FIFO_DEPTH)
) rx_fifos (
    //Clock and reset
    .clk(clk),
    .rst(rst),

    //Connection to the transmitter
    .from_tx(from_tx),

    //DVR interface to the switch routing logic
    .o_v(i_v),
    .o_d(i_d),
    .i_b(i_bp)
);

/* ------------------------------------------------------------------------------------------------
 * Traffic Generation
 * --------------------------------------------------------------------------------------------- */

integer         now = 0;
integer         r;
integer         bp_r [VC_W-1:0];
integer         attempts;
integer         sent;
trace_entry_s   trace [MAX_TRACE_LEN-1:0];

typedef struct packed {
    logic                       valid;
    logic [$clog2(VC_W)-1:0]    vc;
    logic [A_W-1:0]             addr;
    logic [D_W-1:0]             data;
} output_stimulus_s;

typedef struct packed {
    logic [VC_W-1:0]    bp;
} input_stimulus_s;

typedef struct packed {
    output_stimulus_s   out;
    input_stimulus_s    in;
} stimulus_s;
stimulus_s current_stimulus;

initial begin
    //Load default trace if applicable
    if (TRACE_FNAME != "") begin
        load_trace(TRACE_FNAME);
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        sent <= '0;

        //Provide stimulus right after reset
        attempts            <= 1;//Since we are providing stimulus right away
        current_stimulus    <= '{out: get_out_stimulus(), in: '0};
    end else begin
        //We should not update our output stimulus if we're backpressured (must hold them stable)
        if (!o_bp[current_stimulus.out.vc]) begin
            //We actually did send something (we aren't completely done or just not transmitting this cycle)
            if (current_stimulus.out.valid) begin
                $display(
                    "<verif_client>@%0d: Sent SRC_PE=%0d DEST_PE=%0d VC=%0d data/packetid=%0d",
                    now - 1,
                    posx,
                    current_stimulus.out.addr,
                    current_stimulus.out.vc,
                    o_d[D_W-1:0]
                );
                sent <= sent + 1;
            end

            //r is random between 0 and 99, so this throttles the amount of traffic we will send
            //We also stop generating traffic if we are done
            r <= $urandom_range(0, 99);
            if (r < rate && !done) begin
                //Not throttled or finished, obtain new stimulus to send!
                //(Note that this could set valid to 0 as well)
                current_stimulus.out <= get_out_stimulus();
                attempts <= attempts + 1;
                //TODO perhaps print when we try to start sending a packet?
                //TODO deal with the fact attempts should only be incremented if get_oujt_stimulus() set the .valid field
            end else begin
                //Not sending a packet (this clears, among other things, the .valid signal)
                current_stimulus.out <= '0;
            end
        end

        //Potentially backpressure this clock cycle based on the backpressure rate (per VC)
        for (int ii = 0; ii < VC_W; ++ii) begin
            bp_r[ii] <= $urandom_range(0, 99);
            if (bp_r[ii] < bp_rate) begin
                current_stimulus.in.bp[ii] <= 1'b1;
            end else begin
                current_stimulus.in.bp[ii] <= 1'b0;
            end
        end
    end
end

always_comb begin
    o_v                             = '0;
    o_v[current_stimulus.out.vc]    = current_stimulus.out.valid;
    o_d                             = {1'b0, current_stimulus.out.addr, current_stimulus.out.data};
    i_bp                            = current_stimulus.in.bp;
end

/* ------------------------------------------------------------------------------------------------
 * Packet Reciept Logging
 * --------------------------------------------------------------------------------------------- */

always_ff @(posedge clk) begin
    if (!rst) begin
        for (int ii = 0; ii < VC_W; ++ii) begin
            if (i_v[ii] && !i_bp[ii]) begin
                $display(
                    "<verif_client>@%0d: Received PE=%0d VC=%0d data/packetid=%0d",
                    now - 1,
                    posx,
                    ii,
                    i_d[ii][D_W-1:0]
                );
            end
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * Test Starting And Finishing Management
 * --------------------------------------------------------------------------------------------- */

always_ff @(posedge clk) begin
    now <= now + 1;
    if (now == 0 && posx == 0) begin
        $display("<verif_client>@%0d: Info: N=%0d VC_W=%0d", now, N, VC_W);
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        done <= 1'b0;
    end else begin
        if (!done) begin
            if ((traffic_type == TRAFFIC_TYPE_SYNTHETIC) && (attempts == synthetic_limit)) begin
                $display("<verif_client>@%0d: Done PE=%0d attempts=%0d sent=%0d", now, posx, attempts, sent);
                done <= 1'b1;
            end else if ((traffic_type == TRAFFIC_TYPE_TRACE) && trace[sent].stop_bit) begin
                $display("<verif_client>@%0d: Done PE=%0d attempts=%0d sent=%0d", now, posx, attempts, sent);
                done <= 1'b1;
            end else if (traffic_type == TRAFFIC_TYPE_RX_ONLY) begin
                $display("<verif_client>@%0d: Done PE=%0d attempts=%0d sent=%0d", now, posx, attempts, sent);
                done <= 1'b1;
            end
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * Functions
 * --------------------------------------------------------------------------------------------- */

function output_stimulus_s get_out_stimulus();
    if (traffic_type == TRAFFIC_TYPE_SYNTHETIC) begin
        get_out_stimulus.valid  = attempts < synthetic_limit;
        get_out_stimulus.vc     = generate_synthetic_vc();
        get_out_stimulus.addr   = generate_synthetic_addr();
    end else if (traffic_type == TRAFFIC_TYPE_TRACE) begin
        get_out_stimulus.valid  = !trace[sent].stop_bit;
        //TODO add assertions to ensure no overflow
        get_out_stimulus.vc     = ($clog2(VC_W))'(trace[sent].vc);
        get_out_stimulus.addr   = (A_W)'(trace[sent].dest_pe_addr);
    end else if (traffic_type == TRAFFIC_TYPE_RX_ONLY) begin
        get_out_stimulus.valid  = 1'b0;
        get_out_stimulus.vc     = '0;
        get_out_stimulus.addr   = '0;
    end

    //Trace files don't contain data, so this is always synthetic
    get_out_stimulus.data = generate_synthetic_data();
endfunction

function void load_trace(input string trace_filename);
    assert(rst);
    $readmemh(trace_filename, trace);
endfunction

function logic [$clog2(VC_W)-1:0] generate_synthetic_vc();
    //Why does Verilator complain about this here, this is a function...
    //verilator lint_save
    //verilator lint_off BLKSEQ
    logic [$clog2(VC_W)-1:0] candidate_vc;
    candidate_vc = ($clog2(VC_W))'($urandom_range(0, VC_W-1));

    //Everything's backpressured, no possibility to roll for another vc
    if (&o_bp) begin
        return candidate_vc;
    end

    //Otherwise we can re-roll a few times to try to send on a non-backpressured VC
    //TODO perhaps make the max parameterizable?
    //We still sometimes want to not preempt instead of always prempting
    //whenever we can, so this shouldn't be infinity probably
    for (int ii = 0; ii < 2; ++ii) begin
        if (!o_bp[candidate_vc]) begin
            break;
        end

        candidate_vc = ($clog2(VC_W))'($urandom_range(0, VC_W-1));
    end 

    return candidate_vc;
    //verilator lint_restore
endfunction

function logic [A_W-1:0] generate_synthetic_addr();
    case (synthetic_cmd)
        SYNTHETIC_CMD_RANDOM:           return safe_rand_addr();
        SYNTHETIC_CMD_RANDOM_LOCAL:     return safe_local();
        SYNTHETIC_CMD_RANDOM_BITREV:    return (A_W)'(bitrev(posx) % (10)'(N));
        SYNTHETIC_CMD_RANDOM_TORNADO:   return (A_W)'(tornado(posx, N));
    endcase
endfunction

function logic [D_W-1:0] generate_synthetic_data();
    //Instead of this being random, we make it a deterministic packet id to aid in later tracking
    return get_new_packet_id();
endfunction

logic [D_W-1:0] next_id = posx;
function automatic logic [D_W-1:0] get_new_packet_id();//Unique over the lifetime of the sim
    //Modulo counting to avoid conflicts, based on a unique posx
    //static logic [D_W-1:0] next_id = posx;//Not supported in Verilator
    get_new_packet_id = next_id;

    //verilator lint_save
    //verilator lint_off BLKSEQ
    next_id += N;
    //verilator lint_restore
endfunction

function logic [A_W-1:0] safe_rand_addr();
    do begin
        safe_rand_addr = (A_W)'($urandom_range(0, N - 1));
    end while (safe_rand_addr == posx);//Avoids packets to ourselves
endfunction

function logic [A_W-1:0] safe_local();
    do begin
        safe_local = (A_W)'(local_window(local_rnd(posx), N));
    end while (safe_local == posx);//Avoids packets to ourselves
endfunction

function integer local_rnd(input integer i);
    local_rnd = i + {$random} % sigma - sigma/2;
endfunction

function integer local_window(input integer value, input integer max);
    local_window = (value < 0) ? 0 : (value >= max) ? (max-1) : value;
endfunction

function [9:0] bitrev(input [9:0] i);
    bitrev = {i[0], i[1], i[2], i[3], i[4], i[5], i[6], i[7], i[8], i[9]};
endfunction

function integer tornado(input integer i, input integer max);
    tornado = (i + max/2-1) % max;
endfunction

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

//This module is not synthesizable
`ifndef SIMULATION
assert property (@(posedge clk) disable iff (rst) 1'b0);
`endif

//The traffic type and synthetic limit shouldn't change outside of reset
assert property (@(posedge clk) disable iff (rst) $stable(traffic_type));
assert property (@(posedge clk) disable iff (rst) $stable(synthetic_limit));

//Dynamic parameters shouldn't be unknown outside of reset
assert property (@(posedge clk) disable iff (rst) !$isunknown(synthetic_cmd));
assert property (@(posedge clk) disable iff (rst) !$isunknown(rate));
assert property (@(posedge clk) disable iff (rst) !$isunknown(sigma));
assert property (@(posedge clk) disable iff (rst) !$isunknown(traffic_type));
assert property (@(posedge clk) disable iff (rst) !$isunknown(synthetic_limit));

//Other dynamic parameter assertions
`ifndef IVERILOG//iverilog doesn't support |->
assert property (@(posedge clk) disable iff (rst) (traffic_type != TRAFFIC_TYPE_RX_ONLY) |-> rate <= 100);
assert property (@(posedge clk) disable iff (rst) (traffic_type != TRAFFIC_TYPE_RX_ONLY) |-> rate > 0);
assert property (@(posedge clk) disable iff (rst) bp_rate <= 100);
//assert property (@(posedge clk) disable iff (rst) bp_rate >= 0);//Unsigned so this is always true
assert property (@(posedge clk) disable iff (rst) (traffic_type == TRAFFIC_TYPE_SYNTHETIC) |-> (synthetic_limit > 0));
`endif //IVERILOG

//Done sanity checks
assert property (@(posedge clk) disable iff (rst) !$isunknown(done));
`ifndef IVERILOG//iverilog doesn't support |->
//Commented this out because it was firing, perhaps when the destination is
//backpressuring us this isn't always true...
//assert property (@(posedge clk) disable iff (rst) done |-> (o_v == '0));
`ifndef VERILATOR//Verilator doesn't support the `throughout` keyword
assert property (@(posedge clk) disable iff (rst) done |-> done throughout rst[->1]);
`endif //VERILATOR
`endif //IVERILOG

//Stimulus sanity checks
assert property (@(posedge clk) disable iff (rst) !$isunknown(current_stimulus));
assert property (@(posedge clk) disable iff (rst) ($clog2(VC_W)+1)'(current_stimulus.out.vc) < ($clog2(VC_W)+1)'(VC_W));

//Valid shouldn't be deasserted while we are being backpressured if we have already asserted it
`ifndef IVERILOG//iverilog doesn't support |->
`ifndef VERILATOR//Verilator doesn't support the `throughout` keyword
generate
for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_assert_nice_valid
    assert property (@(posedge clk) disable iff (rst) o_v[ii] |-> (o_v[ii] throughout (!o_bp[ii])[->1]));
end : gen_assert_nice_valid
endgenerate
`endif //VERILATOR
`endif //IVERILOG

//TODO more

endmodule : verif_client
