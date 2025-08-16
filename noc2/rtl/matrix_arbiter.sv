/*
 * File:    matrix_arbiter.sv
 * Brief:   Matrix arbiter implementation
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Inspired by design in section 18.5 of Principles and Practices of
 * Interconnection Networks by William Dally and Brian Towles
 *
 * ii indicies are rows, and jj indicies are columns
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module matrix_arbiter #(
    parameter NUM = 4//Number of request/grant signals
) (
    //Clock and reset
    input   logic clk,
    input   logic rst,

    //Request and grant signals
    input   logic [NUM-1:0] i_req,
    output  logic [NUM-1:0] o_gnt
);

//_ Verilator _thinks_ there is a combinational loop here because we're
//using the same vectors, HOWEVER we are using different _bits_ of the
//vectors so this is not the case. Vivado synthesis confirms this.
//It also complains about one of the always blocks for a similar reason.
//So just quiet Verilator on these messages since it is buggy
//verilator lint_save
//verilator lint_off UNOPTFLAT
//verilator lint_off ALWCOMBORDER
//verilator lint_off MULTIDRIVEN

/* ------------------------------------------------------------------------------------------------
 * Common Signals
 * --------------------------------------------------------------------------------------------- */

//"Triangular array":
//- The diagonal isn't used (we just assign each of these to 0)
//- The lower triangle is simply the complement of the upper triangle
//- The upper triangle are the actual state flops
//- To work around Verilator limitations, we have two of these to avoid
//blocking and non-blocking assignments to the same vector
logic [NUM-1:0][NUM-1:0] state_matrix;
logic [NUM-1:0][NUM-1:0] matrix;

//Disable lines per the design
logic [NUM-1:0] dis;

/* ------------------------------------------------------------------------------------------------
 * Upper Triangle
 * --------------------------------------------------------------------------------------------- */

always_ff @(posedge clk) begin
    if (rst) begin
        for (int ii = 0; ii < NUM; ++ii) begin
            for (int jj = 0; jj < NUM; ++jj) begin
                state_matrix[ii][jj] <= 1'b0;
            end
        end
    end else begin
        for (int ii = 0; ii < (NUM - 1); ++ii) begin
            for (int jj = ii + 1; jj < NUM; ++jj) begin
                //Straight from the design:
                //We clear a row when a request is granted, thereby (via the
                //mirroring) setting all bits in our column. This effectively
                //gives us the lowest priority since this makes it more likely
                //that we'll be disabled by another request (until, that is,
                //another request is granted, in which case it will set the
                //relevant bit in our row to indicate we're no longer the most
                //recently granted request).
                state_matrix[ii][jj] <= (state_matrix[ii][jj] | o_gnt[jj]) & ~o_gnt[ii];
            end
        end
    end
end

//Workaround for Verilator:
always_comb begin
    for (int ii = 0; ii < (NUM - 1); ++ii) begin
        for (int jj = ii + 1; jj < NUM; ++jj) begin
            matrix[ii][jj] = state_matrix[ii][jj];
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * Diagonal Zeroing and Triangle Mirroring
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    //Zeroing out the diagonal makes the anded_matrix easier to implement
    for (int ii = 0; ii < NUM; ++ii) begin
        matrix[ii][ii] = 1'b0;
    end
end

always_comb begin
    //The lower triangle is the complement of the upper triangle as discussed previously
    for (int ii = 1; ii < NUM; ++ii) begin
        for (int jj = 0; jj < ii; ++jj) begin
            //Must be `state_matrix` and not `matrix` because of iverilog/sv2v bugs
            matrix[ii][jj] = ~state_matrix[jj][ii];
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * Disable Signal Generation
 * --------------------------------------------------------------------------------------------- */

//The `matrix` but with all of the bits in a given row anded with the corresponding request signal
//We also transpose it so that we can easily or the columns
logic [NUM-1:0][NUM-1:0] anded_transposed_matrix;

always_comb begin
    for (int ii = 0; ii < NUM; ++ii) begin
        for (int jj = 0; jj < NUM; ++jj) begin
            anded_transposed_matrix[jj][ii] = matrix[ii][jj] & i_req[ii];
        end
    end
end

//The disables are just the ors of each column
always_comb begin
    for (int jj = 0; jj < NUM; ++jj) begin
        dis[jj] = |anded_transposed_matrix[jj];
    end
end

/* ------------------------------------------------------------------------------------------------
 * Grant Signals
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    //We only grant if there's a request and there's not another higher priority request
    for (int ii = 0; ii < NUM; ++ii) begin
        o_gnt[ii] = i_req[ii] & ~dis[ii];
    end
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Control signals should be known out of reset
assert property (@(posedge clk) disable iff (rst) !$isunknown(i_req));
assert property (@(posedge clk) disable iff (rst) !$isunknown(o_gnt));

//Grant signals are one-hot or 0
assert property (@(posedge clk) disable iff (rst) $onehot0(o_gnt));

generate
for (genvar ii = 0; ii < NUM; ++ii) begin : gen_assertions
    //Never grant unless requested
    assert property (@(posedge clk) disable iff (rst) o_gnt[ii] |-> i_req[ii]);

    //No deasserting request once asserted until granted
    //TODO enable this check once it plays a bit better with testbenches
`ifndef IVERILOG//iverilog doesn't support |->
`ifndef VERILATOR//Verilator doesn't support the `throughout` keyword
    //assert property (@(posedge clk) disable iff (rst) i_req[ii] |-> (i_req[ii] throughout o_gnt[ii][->1]));
`endif //VERILATOR
`endif //IVERILOG
end
endgenerate

`endif //SIMULATION

//verilator lint_restore

endmodule : matrix_arbiter
