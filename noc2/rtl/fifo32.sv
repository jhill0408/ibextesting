/*
 * File:    fifo32.sv
 * Brief:   FIFO primitive, 32-entry depth granularity
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Useful for abstracting a FIFO primitive of the target implementation technology
 *
 * Avaiable technologies (TECH):
 * - FIFO18E1
 * - FIFO18E2
 * - RTL
 * - TODO more options (LUTRAM, BRAM + fabric logic, ASIC SRAM based, etc.)
 * - TODO lutram based, super minimal lut usage
 *
 * Note that while two FIFO18s can't go into the same BRAM, if you make one of
 * your FIFOs a FIFO18 and the other an RTL, they can share the same BRAM
 * (provided the RTL infers a RAMB18 correctly, which it should)
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module fifo32 #(
    parameter int       DEPTH32     = 4,//Actual depth is DEPTH32 * 32 - 1
    parameter int       WIDTH       = 32,
    parameter string    TECH        = "RTL",
    parameter int       RLATENCY    = 0//Read latency (0 means combinational, AKA FWFT)
) (
    //Clock and reset
    input   logic clk,
    input   logic rst,

    //Push interface, 1-cycle latency
    input   logic               i_push,
    output  logic               o_full,
    input   logic [WIDTH-1:0]   i_wdata,

    //Pop interface, 1-cycle latency
    input   logic               i_pop,
    output  logic               o_empty,
    output  logic [WIDTH-1:0]   o_rdata
);

localparam int DEPTH = DEPTH32 * 32;//Actual depth is this - 1

generate
    if (TECH == "FIFO18E1") begin : gen_fifo18e1
        //TODO support larger widths, depths (instanciate multiple FIFO18E1s)
        logic [31:0] DO;
        logic [3:0]  DOP;//TODO also use this as extra data!
        logic        EMPTY;
        logic        FULL;
        logic        RDCLK;
        logic        RDEN;
        //logic        REGCE;
        logic        RST;
        logic        WRCLK;
        logic        WREN;
        logic [31:0] DI;
        logic [3:0]  DIP;//TODO also use this as extra data!

        always_comb begin
            o_rdata = DO;
            o_empty = EMPTY;
            o_full  = FULL;
            RDCLK   = clk;
            RDEN    = i_pop;
            RST     = rst;//FIXME rst is not async!
            WRCLK   = clk;
            WREN    = i_push;
            DI      = i_wdata;
        end

        //Instanciation based on https://docs.amd.com/r/en-US/ug953-vivado-7series-libraries/FIFO18E1
        FIFO18E1 #(
           .DATA_WIDTH(36),                         //Sets data width to 4-36
           .FIFO_MODE("FIFO18"),                    //Sets mode to FIFO18 or FIFO18_36
           .FIRST_WORD_FALL_THROUGH(RLATENCY == 0)  //Sets the FIFO FWFT to FALSE, TRUE
        ) fifo (
           //verilator lint_save
           //verilator lint_off PINCONNECTEMPTY
           //Read Data: 32-bit (each) output: Read output data
           .DO(DO),         //32-bit output: Data output
           .DOP(DOP),       //4-bit output: Parity data output
           //Status: 1-bit (each) output: Flags and other FIFO status outputs
           .ALMOSTEMPTY(),  //1-bit output: Almost empty flag//NU
           .ALMOSTFULL(),   //1-bit output: Almost full flag//NU
           .EMPTY(EMPTY),   //1-bit output: Empty flag
           .FULL(FULL),     //1-bit output: Full flag
           .RDCOUNT(),      //12-bit output: Read count//NU
           .RDERR(),        //1-bit output: Read error//NU
           .WRCOUNT(),      //12-bit output: Write count//NU
           .WRERR(),        //1-bit output: Write error//NU
           //Read Control Signals: 1-bit (each) input: Read clock, enable and reset input signals
           .RDCLK(RDCLK),   //1-bit input: Read clock
           .RDEN(RDEN),     //1-bit input: Read enable
           .REGCE(1'b1),    //1-bit input: Clock enable//NU//TODO this could help save power
           .RST(RST),       //1-bit input: Asynchronous Reset
           .RSTREG(1'b0),   //1-bit input: Output register set/reset//NU
           //Write Control Signals: 1-bit (each) input: Write clock and enable input signals
           .WRCLK(WRCLK),   //1-bit input: Write clock
           .WREN(WREN),     //1-bit input: Write enable
           //Write Data: 32-bit (each) input: Write input data
           .DI(DI),         //32-bit input: Data input
           .DIP(DIP)        //4-bit input: Parity input
           //verilator lint_restore
        );
    end : gen_fifo18e1
    //else if (TECH == "FIFO18E2") begin : gen_fifo18e2
        //TODO use https://docs.amd.com/r/en-US/ug974-vivado-ultrascale-libraries/FIFO18E2
    //end : gen_fifo18e2
    else if (TECH == "RTL") begin : gen_rtl
        logic [WIDTH-1:0]           fifo_data [DEPTH-1:0];//Unpacked array to make it more likely to infer SRAM
        logic [$clog2(DEPTH)-1:0]   fifo_head, fifo_tail, next_fifo_head, next_fifo_tail;

        always_comb begin
            //The DEPTH is always a power of 2 so we can rely on wrapping
            next_fifo_head = fifo_head + ($clog2(DEPTH))'(1);
            next_fifo_tail = fifo_tail + ($clog2(DEPTH))'(1);

            //Worse timing if we do these combinatinationally
            //o_full  = next_fifo_head == fifo_tail;//Next push would make it indistinguishable from empty
            //o_empty = fifo_head == fifo_tail;
        end

        //Instead, put the comparisons behind flops :)
        always_ff @(posedge clk) begin
            if (rst) begin
                o_full  <= 1'b0;
                o_empty <= 1'b1;
            end else begin
                if (i_push && i_pop) begin
                    o_full  <= (next_fifo_head + ($clog2(DEPTH))'(1)) == next_fifo_tail;
                    o_empty <=  next_fifo_head                        == next_fifo_tail;
                end else if (i_push) begin
                    o_full  <= (next_fifo_head + ($clog2(DEPTH))'(1)) ==      fifo_tail;
                    o_empty <=  next_fifo_head                        ==      fifo_tail;
                end else if (i_pop) begin
                    o_full  <=  next_fifo_head                        == next_fifo_tail;
                    o_empty <=       fifo_head                        == next_fifo_tail;
                end
            end
        end

        always_ff @(posedge clk) begin
            if (rst) begin
                fifo_head   <= '0;
                fifo_tail   <= '0;
            end else begin
                if (i_push) begin
                    fifo_head <= next_fifo_head;
                end

                if (i_pop) begin
                    fifo_tail <= next_fifo_tail;
                end
            end
        end

        //Seperate always_ff to make it more likely to infer SRAM
        always_ff @(posedge clk) begin
            if (i_push) begin
                fifo_data[fifo_head] <= i_wdata;//Input demux (1-cycle latency)
            end
        end

        if (RLATENCY == 0) begin : gen_rlatency0
            assign o_rdata = fifo_data[fifo_tail];//Output mux (0-cycle latency)
        end : gen_rlatency0
        else begin : gen_rlatency1
            always_ff @(posedge clk) begin
                if (i_pop) begin
                    o_rdata <= fifo_data[fifo_tail];//Output mux (1-cycle latency)
                end
            end
        end : gen_rlatency1
    end : gen_rtl
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Control signals should be known out of reset
assert property (@(posedge clk) disable iff (rst) !$isunknown(i_push));
assert property (@(posedge clk) disable iff (rst) !$isunknown(i_pop));
assert property (@(posedge clk) disable iff (rst) !$isunknown(o_empty));
assert property (@(posedge clk) disable iff (rst) !$isunknown(o_full));

//Fundamental FIFO integrity assertions
assert property (@(posedge clk) disable iff (rst) !(o_empty && i_pop));
assert property (@(posedge clk) disable iff (rst) !(o_full  && i_push));

//Qualified data shouldn't be unknown when valid
assert property (@(posedge clk) disable iff (rst) (i_push   |-> !$isunknown(i_wdata)));
assert property (@(posedge clk) disable iff (rst) (!o_empty |-> !$isunknown(o_rdata)));

`endif //SIMULATION

endmodule : fifo32
