/*
 * File:    experiment_mux4x2_mux6x2_pi.sv
 * Brief:   FPGA mapping experiment: Using 2 Mux4s + 2 Mux6s for the pi switch where VC_W = 2
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Comparing this with hieraricherial Mux2s and Mux3s
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module experiment_mux4x2_mux6x2_pi
    import common_pkg::*;
#(
    parameter A_W = DEFAULT_A_W,
    parameter D_W = DEFAULT_D_W
) (
    input  logic [1:0][2:0]         lr_s,
    input  logic [1:0][A_W+D_W:0]   lr_i0,
    input  logic [1:0][A_W+D_W:0]   lr_i1,
    input  logic [1:0][A_W+D_W:0]   lr_i2,
    input  logic [1:0][A_W+D_W:0]   lr_i3,
    input  logic [1:0][A_W+D_W:0]   lr_i4,
    input  logic [1:0][A_W+D_W:0]   lr_i5,
    output logic [1:0][A_W+D_W:0]   lr_o,

    input  logic [1:0][1:0]         u0u1_s,
    input  logic [1:0][A_W+D_W:0]   u0u1_i0,
    input  logic [1:0][A_W+D_W:0]   u0u1_i1,
    input  logic [1:0][A_W+D_W:0]   u0u1_i2,
    input  logic [1:0][A_W+D_W:0]   u0u1_i3,
    output logic [1:0][A_W+D_W:0]   u0u1_o
);

generate
for (genvar ii = 0; ii < 2; ++ii) begin : gen_mux6
    mux #(
        .N(6),
        .W(A_W+D_W+1)
    ) mux6 (
        .s(lr_s[ii]),
        .i({lr_i5[ii], lr_i4[ii], lr_i3[ii], lr_i2[ii], lr_i1[ii], lr_i0[ii]}),
        .o(lr_o[ii])
    );
end : gen_mux6
endgenerate

generate
for (genvar ii = 0; ii < 2; ++ii) begin : gen_mux4
    mux #(
        .N(4),
        .W(A_W+D_W+1)
    ) mux4 (
        .s(u0u1_s[ii]),
        .i({u0u1_i3[ii], u0u1_i2[ii], u0u1_i1[ii], u0u1_i0[ii]}),
        .o(u0u1_o[ii])
    );
end : gen_mux4
endgenerate

endmodule : experiment_mux4x2_mux6x2_pi
