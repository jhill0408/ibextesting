/*
 * File:    experiment_mux4x3_t.sv
 * Brief:   FPGA mapping experiment: Using 3 Mux4s for the t switch where VC_W = 2
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Comparing this with hieraricherial Mux2s
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module experiment_mux4x3_t
    import common_pkg::*;
#(
    parameter A_W = DEFAULT_A_W,
    parameter D_W = DEFAULT_D_W
) (
    input  logic [2:0][1:0]         s,
    input  logic [2:0][A_W+D_W:0]   i0,
    input  logic [2:0][A_W+D_W:0]   i1,
    input  logic [2:0][A_W+D_W:0]   i2,
    input  logic [2:0][A_W+D_W:0]   i3,
    output logic [2:0][A_W+D_W:0]   o
);

generate
for (genvar ii = 0; ii < 3; ++ii) begin : gen_mux4
    mux #(
        .N(4),
        .W(A_W+D_W+1)
    ) mux4 (
        .s(s[ii]),
        .i({i3[ii], i2[ii], i1[ii], i0[ii]}),
        .o(o[ii])
    );
end : gen_mux4
endgenerate

endmodule : experiment_mux4x3_t
