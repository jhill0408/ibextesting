/**
 * File    credit_bp_tx_tb.sv
 * Brief   credit_bp_tx testbench
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Based on credit_bp_rx_tb
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Macros
 * --------------------------------------------------------------------------------------------- */

`define WAITN(n) repeat(n) @(negedge clk)

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module credit_bp_tx_tb;

import common_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam  CLOCK_PERIOD = 10;

localparam  VC_W  = DEFAULT_VC_W;
localparam  D_W   = DEFAULT_D_W;
localparam  A_W   = DEFAULT_A_W;
localparam  DEPTH = DEFAULT_VC_FIFO_DEPTH;//Actual depth is this - 1

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;
logic rst = 1'b1;//To ensure rst is asserted at the beginning of the sim

//Connection to the receiver 
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) to_rx (
    .*
);

//DVR interface from the switch routing logic
logic [VC_W-1:0]    i_v;//One valid signal per VC
logic [A_W+D_W:0]   i_d;//Data, address, and last signals are per VC; assume the switch has arbitrated this//TODO update other RTL and make this a noc_packet_s instead
logic [VC_W-1:0]    o_b;//And so too are the backpressure signals

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

credit_bp_tx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(DEPTH)
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

always @(posedge clk) begin
    $display(
        "t=%t rst=%b vc_target=%b packet={%h,%h,%h} vc_credit_gnt=%b i_v=%b i_d={%h,%h,%h} o_b=%b",
        $time, rst, to_rx.vc_target,
        to_rx.packet.payload.data, to_rx.packet.payload.last, to_rx.packet.routeinfo.addr,
        to_rx.vc_credit_gnt, i_v,
        i_d[D_W-1:0], i_d[D_W+A_W-1:D_W], i_d[A_W+D_W],
        o_b
    );
end

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Assert reset for a couple clock cycles, and set initial inputs
    rst                 <= 1'b1;
    to_rx.vc_credit_gnt <= '0;
    i_v                 <= '0;
    i_d                 <= '0;
    `WAITN(2);
    rst <= 1'b0;
    `WAITN(2);
    assert(o_b == '0);//Right after reset we should have credits!
    assert(to_rx.vc_target == '0);//There's nothing to be sent though

    //Spend a VC0 credit!
    i_v <= 2'b01;
    i_d <= {1'b1, 4'h3, 32'h12344321};
    #(CLOCK_PERIOD / 4);//Data is passed through combinationally
    assert(o_b                          == '0);//Haven't used a credit until the posedge
    assert(to_rx.vc_target              == 2'b01);
    assert(to_rx.packet.payload.data    == 32'h12344321);
    assert(to_rx.packet.routeinfo.addr  == 4'h3);
    assert(to_rx.packet.payload.last    == 1'b1);
    `WAITN(1);
    assert(o_b == '0);//We should still have credits left

    //Spend a VC1 credit while giving VC0 its credit back!
    i_v                 <= 2'b10;
    i_d                 <= {1'b0, 4'h2, 32'hABCDDCBA};
    to_rx.vc_credit_gnt <= 2'b01;
    #(CLOCK_PERIOD / 4);//Data is passed through combinationally
    assert(o_b                          == '0);
    assert(to_rx.vc_target              == 2'b10);
    assert(to_rx.packet.payload.data    == 32'hABCDDCBA);
    assert(to_rx.packet.routeinfo.addr  == 4'h2);
    assert(to_rx.packet.payload.last    == 1'b0);
    `WAITN(1);

    //Give VC1 a credit back while spending another VC0 credit
    i_v                 <= 2'b01;
    i_d                 <= {1'b0, 4'h1, 32'h98766789};
    to_rx.vc_credit_gnt <= 2'b10;
    #(CLOCK_PERIOD / 4);//Data is passed through combinationally
    assert(o_b                          == '0);
    assert(to_rx.vc_target              == 2'b01);
    assert(to_rx.packet.payload.data    == 32'h98766789);
    assert(to_rx.packet.routeinfo.addr  == 4'h1);
    assert(to_rx.packet.payload.last    == 1'b0);
    `WAITN(1);
    assert(o_b == '0);

    //Spend and grant a VC0 credit on the same cycle
    i_v                 <= 2'b01;
    i_d                 <= {1'b1, 4'h0, 32'hFEDCBA98};
    to_rx.vc_credit_gnt <= 2'b01;
    #(CLOCK_PERIOD / 4);//Data is passed through combinationally
    assert(o_b                          == '0);
    assert(to_rx.vc_target              == 2'b01);
    assert(to_rx.packet.payload.data    == 32'hFEDCBA98);
    assert(to_rx.packet.routeinfo.addr  == 4'h0);
    assert(to_rx.packet.payload.last    == 1'b1);
    `WAITN(1);
    assert(o_b == '0);

    //Grant back a VC0 credit. We should be back to the beginning!
    i_v                 <= '0;
    i_d                 <= '0;
    to_rx.vc_credit_gnt <= 2'b01;
    `WAITN(1);
    assert(o_b == '0);
    assert(to_rx.vc_target == '0);
    
    //Exhaust VC0 credits
    i_v                 <= 2'b01;
    to_rx.vc_credit_gnt <= '0;
    for (int ii = 0; ii < DEPTH - 1; ++ii) begin
        i_d <= {(1)'(ii * 123), (A_W)'(ii * 123), (D_W)'(ii * 123)};
        #(CLOCK_PERIOD / 4);//Data is passed through combinationally
        assert(o_b                          == '0);//Won't update until the posedge
        assert(to_rx.vc_target              == 2'b01);
        assert(to_rx.packet.payload.data    == (D_W)'(ii * 123));
        assert(to_rx.packet.routeinfo.addr  == (A_W)'(ii * 123));
        assert(to_rx.packet.payload.last    ==   (1)'(ii * 123));
        `WAITN(1);
    end
    assert(o_b              == 2'b01);//We should be out of credits now
    assert(to_rx.vc_target  == '0);//The DUT should be refusing to send more
    `WAITN(3);
    //Nothing should have changed even after a few cycles
    assert(o_b              == 2'b01);
    assert(to_rx.vc_target  == '0);

    //But we should still be able to push to VC1! Exhaust it as well.
    i_v <= 2'b10;
    to_rx.vc_credit_gnt <= '0;
    for (int ii = 0; ii < DEPTH - 1; ++ii) begin
        i_d <= {(1)'(ii * 456), (A_W)'(ii * 456), (D_W)'(ii * 456)};
        #(CLOCK_PERIOD / 4);//Data is passed through combinationally
        assert(o_b                          == 2'b01);//Won't update until the posedge
        assert(to_rx.vc_target              == 2'b10);
        assert(to_rx.packet.payload.data    == (D_W)'(ii * 456));
        assert(to_rx.packet.routeinfo.addr  == (A_W)'(ii * 456));
        assert(to_rx.packet.payload.last    ==   (1)'(ii * 456));
        `WAITN(1);
    end
    assert(o_b              == 2'b11);//Now we have no credits left at all!
    assert(to_rx.vc_target  == '0);//The DUT should be refusing to send more data
    `WAITN(3);
    //Nothing should have changed even after a few cycles
    assert(o_b              == 2'b11);
    assert(to_rx.vc_target  == '0);

    //Grant back credits to both at the same time!
    i_v                 <= '0;
    i_d                 <= '0;
    to_rx.vc_credit_gnt <= 2'b11;
    for (int ii = 0; ii < DEPTH - 1; ++ii) begin
        `WAITN(1);
        assert(o_b              == '0);//We shouldn't be backpressured as long as we have one credit
        assert(to_rx.vc_target  == '0);
    end

    //Back to the beginning!
    to_rx.vc_credit_gnt <= '0;
    assert(o_b              == '0);
    assert(to_rx.vc_target  == '0);
    `WAITN(3);
    //After idling, nothing should have changed
    assert(o_b              == '0);
    assert(to_rx.vc_target  == '0);

    `WAITN(5);
    $finish;

    //verilator lint_restore
end

endmodule : credit_bp_tx_tb
