/**
 * File    matrix_arbiter_tb.sv
 * Brief   matrix_arbiter testbench
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

`define WAITN(n) repeat(n) @(negedge clk)

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module matrix_arbiter_tb;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam NUM = 4;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;
logic rst = 1'b1;//To ensure rst is asserted at the beginning of the sim

logic [NUM-1:0] i_req;
logic [NUM-1:0] o_gnt;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

matrix_arbiter #(
    .NUM(NUM)
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
       "t=%t rst=%b i_req=%b o_gnt=%b",
        $time, rst, i_req, o_gnt
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
    i_req   <= '0;
    `WAITN(2);
    rst <= 1'b0;
    `WAITN(2);

    //No grants should be asserted while no requests are made
    assert(o_gnt == 4'b0000);

    //Only a single request being made, it will be continually serviced
    for (int ii = 0; ii < 10; ++ii) begin
        for (logic [NUM-1:0] jj = 4'b0001; jj != '0; jj <<= 1) begin
            i_req <= jj;
            #(CLOCK_PERIOD / 4);//This will occur combinationaly
            for (int kk = 0; kk < 10; ++kk) begin
                `WAITN(1);
                assert(o_gnt == jj);
            end
        end
    end

    //Ensure things have stopped
    i_req <= 4'b0000;
    #(CLOCK_PERIOD / 4);//This will occur combinationaly
    assert(o_gnt == 4'b0000);

    //Since we each request an equal number of times in the loop above, this
    //means that the most recent grants were: 3, 2, 1, 0. So we can expect
    //0 first here, then 1, then 2, then 3, and so on
    i_req <= 4'b1111;
    #(CLOCK_PERIOD / 4);//This will occur combinationaly
    for (int ii = 0; ii < 10; ++ii) begin
        for (logic [NUM-1:0] jj = 4'b0001; jj != '0; jj <<= 1) begin
            assert(o_gnt == jj);
            `WAITN(1);
        end
    end
    i_req <= 4'b0000;
    #(CLOCK_PERIOD / 4);
    assert(o_gnt == 4'b0000);

    //Let's give 2 a turn
    i_req <= 4'b0100;
    `WAITN(1);
    assert(o_gnt == 4'b0100);
    i_req <= 4'b0000;
    #(CLOCK_PERIOD / 4);
    assert(o_gnt == 4'b0000);

    //Now we expect the order to be 0, 1, 3, 2
    i_req <= 4'b1111;
    #(CLOCK_PERIOD / 4);
    for (int ii = 0; ii < 10; ++ii) begin
        assert(o_gnt == 4'b0001);
        `WAITN(1);
        assert(o_gnt == 4'b0010);
        `WAITN(1);
        assert(o_gnt == 4'b1000);
        `WAITN(1);
        assert(o_gnt == 4'b0100);
        `WAITN(1);
    end
    i_req <= 4'b0000;
    #(CLOCK_PERIOD / 4);
    assert(o_gnt == 4'b0000);

    //Now let's do 1
    i_req <= 4'b0010;
    `WAITN(1);
    assert(o_gnt == 4'b0010);
    i_req <= 4'b0000;
    #(CLOCK_PERIOD / 4);
    assert(o_gnt == 4'b0000);

    //Now we expect the order to be 0, 3, 2, 1, but since we're not enabling 0,
    //it should just be 3, 2, 1
    i_req <= 4'b1110;
    #(CLOCK_PERIOD / 4);
    for (int ii = 0; ii < 10; ++ii) begin
        assert(o_gnt == 4'b1000);
        `WAITN(1);
        assert(o_gnt == 4'b0100);
        `WAITN(1);
        assert(o_gnt == 4'b0010);
        `WAITN(1);
    end
    i_req <= 4'b0000;
    #(CLOCK_PERIOD / 4);
    assert(o_gnt == 4'b0000);

    `WAITN(5);
    $finish;

    //verilator lint_restore
end

endmodule : matrix_arbiter_tb
