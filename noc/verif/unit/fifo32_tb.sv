/**
 * File    fifo32_tb.sv
 * Brief   fifo32 testbench
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

module fifo32_tb;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam  CLOCK_PERIOD = 10;

localparam  DEPTH32     = 4;//Actual depth is DEPTH32 * 32 - 1
localparam  WIDTH       = 32;
localparam  TECH        = "RTL";//Needs to be RTL for simulation purposes
localparam  RLATENCY    = 0;//Read latency (0 means combinational, AKA FWFT)

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;
logic rst = 1'b1;//To ensure rst is asserted at the beginning of the sim

//Push interface, 1-cycle latency
logic               i_push;
logic               o_full;
logic [WIDTH-1:0]   i_wdata;

//Pop interface, 1-cycle latency
logic               i_pop;
logic               o_empty;
logic [WIDTH-1:0]   o_rdata;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

fifo32 #(
    .DEPTH32(DEPTH32),
    .WIDTH(WIDTH),
    .TECH(TECH),
    .RLATENCY(RLATENCY)
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
       "t=%t rst=%b i_push=%b o_full=%b i_wdata=%h i_pop=%b o_empty=%b o_rdata=%h",
        $time, rst, i_push,   o_full,   i_wdata,   i_pop,   o_empty,   o_rdata
    );
end

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Assert reset for a couple clock cycles, and set initial inputs
    rst     <= 1'b1;
    i_push  <= '0;
    i_wdata <= '0;
    i_pop   <= '0;
    `WAITN(2);
    rst <= 1'b0;
    `WAITN(2);
    assert(o_empty == 1'b1);//Right after reset there shouldn't be any data
    assert(o_full  == 1'b0);

    //Push something!
    i_push  <= 1'b1;
    i_wdata <= 32'hA5A5A5A5;
    `WAITN(1);
    assert(o_empty == 1'b0);//We should have data now
    assert(o_full  == 1'b0);//But we're not full yet
    assert(o_rdata == 32'hA5A5A5A5);//0 cycles of read latency
    i_push  <= 1'b0;
    i_wdata <= '0;

    //Pop what we just pushed
    i_pop <= 1'b1;
    `WAITN(1);
    assert(o_empty == 1'b1);//Empty again
    assert(o_full  == 1'b0);//And thus not full
    //The data is gone though now!
    i_pop <= 1'b0;

    //Back-to-back pushes
    i_push  <= 1'b1;
    i_wdata <= 32'h11111111;
    `WAITN(1);
    assert(o_empty == 1'b0);
    assert(o_full  == 1'b0);
    assert(o_rdata == 32'h11111111);
    i_wdata <= 32'h22222222;
    `WAITN(1);
    assert(o_empty == 1'b0);
    assert(o_full  == 1'b0);
    assert(o_rdata == 32'h11111111);//Haven't popped yet!
    i_wdata <= 32'h33333333;
    `WAITN(1);
    assert(o_empty == 1'b0);
    assert(o_full  == 1'b0);
    assert(o_rdata == 32'h11111111);//Still haven't popped yet!
    i_push  <= 1'b0;
    i_wdata <= '0;

    //Back-to-back pops
    i_pop <= 1'b1;
    `WAITN(1);
    assert(o_empty == 1'b0);
    assert(o_full  == 1'b0);
    assert(o_rdata == 32'h22222222);//Popped the 32'h11111111
    `WAITN(1);
    assert(o_empty == 1'b0);
    assert(o_full  == 1'b0);
    assert(o_rdata == 32'h33333333);//Popped the 32'h22222222
    `WAITN(1);
    assert(o_empty == 1'b1);
    assert(o_full  == 1'b0);
    i_pop <= 1'b0;

    //Interleaved push and pop
    i_push  <= 1'b1;
    i_wdata <= 32'hAAAAAAAA;
    `WAITN(1);
    assert(o_empty == 1'b0);
    assert(o_full  == 1'b0);
    assert(o_rdata == 32'hAAAAAAAA);
    i_push  <= 1'b1;
    i_wdata <= 32'hBBBBBBBB;
    i_pop   <= 1'b1;
    `WAITN(1);
    assert(o_empty == 1'b0);
    assert(o_full  == 1'b0);
    assert(o_rdata == 32'hBBBBBBBB);
    i_push  <= 1'b1;
    i_wdata <= 32'hCCCCCCCC;
    i_pop   <= 1'b1;
    `WAITN(1);
    assert(o_empty == 1'b0);
    assert(o_full  == 1'b0);
    assert(o_rdata == 32'hCCCCCCCC);
    i_push  <= 1'b1;
    i_wdata <= 32'hDDDDDDDD;
    i_pop   <= 1'b0;//Taking a break from popping
    `WAITN(1);
    assert(o_empty == 1'b0);
    assert(o_full  == 1'b0);
    assert(o_rdata == 32'hCCCCCCCC);
    i_push  <= 1'b0;//Done pushing
    i_wdata <= '0;
    i_pop   <= 1'b1;//Resuming popping (this will pop the 32'hCCCCCCCC)
    `WAITN(1);
    assert(o_empty == 1'b0);
    assert(o_full  == 1'b0);
    assert(o_rdata == 32'hDDDDDDDD);
    i_pop   <= 1'b1;
    `WAITN(1);
    assert(o_empty == 1'b1);
    assert(o_full  == 1'b0);
    i_pop <= 1'b0;

    //Capacity test (also tests wrap-around)
    for (int ii = 0; ii < (DEPTH32 * 32) - 1; ++ii) begin
        i_push  <= 1'b1;
        i_wdata <= ii * 123;
        `WAITN(1);
    end
    i_push  <= 1'b0;
    i_wdata <= '0;
    i_pop   <= 1'b1;
    for (int ii = 0; ii < (DEPTH32 * 32) - 1; ++ii) begin
        assert(o_empty == 1'b0);
        assert(o_full  == (ii == 0 ? 1'b1 : 1'b0));//No longer full after the first pop
        assert(o_rdata == ii * 123);
        `WAITN(1);//The pop actually happens here
    end
    i_pop <= 1'b0;
    assert(o_empty == 1'b1);
    assert(o_full  == 1'b0);

    `WAITN(5);
    $finish;

    //verilator lint_restore
end

endmodule : fifo32_tb
