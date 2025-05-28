/*
 * File:    experiment_hier_mux_pi.sv
 * Brief:   FPGA mapping experiment: Using 6 Mux2s + 2 Mux3s for the pi switch where VC_W = 2
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Comparing this with 2 Mux4s + 2 Mux6s
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module experiment_hier_mux_pi
    import common_pkg::*;
#(
    parameter A_W = DEFAULT_A_W,
    parameter D_W = DEFAULT_D_W
) (
    input  logic                     l_input_which_vc,
    input  logic                     r_input_which_vc,
    input  logic                    u0_input_which_vc,
    input  logic                    u1_input_which_vc,
    input  logic [1:0][A_W+D_W:0]    l_input_vc_packet,
    input  logic [1:0][A_W+D_W:0]    r_input_vc_packet,
    input  logic [1:0][A_W+D_W:0]   u0_input_vc_packet,
    input  logic [1:0][A_W+D_W:0]   u1_input_vc_packet,

    input  logic [1:0]               l_output_which_dir,
    input  logic [1:0]               r_output_which_dir,
    input  logic                    u0_output_which_dir,
    input  logic                    u1_output_which_dir,
    output logic [A_W+D_W:0]         l_output_packet,
    output logic [A_W+D_W:0]         r_output_packet,
    output logic [A_W+D_W:0]        u0_output_packet,
    output logic [A_W+D_W:0]        u1_output_packet
);

/* ------------------------------------------------------------------------------------------------
 * Input Muxes (Muxing between the VCs WITHIN an input direction)
 * --------------------------------------------------------------------------------------------- */

logic [A_W+D_W:0]  l_input_selected_vc;
logic [A_W+D_W:0]  r_input_selected_vc;
logic [A_W+D_W:0] u0_input_selected_vc;
logic [A_W+D_W:0] u1_input_selected_vc;

mux #(
    .N(2),
    .W(A_W+D_W+1)
) l_input_mux (
    .s(l_input_which_vc),
    .i(l_input_vc_packet),
    .o(l_input_selected_vc)
);

mux #(
    .N(2),
    .W(A_W+D_W+1)
) r_input_mux (
    .s(r_input_which_vc),
    .i(r_input_vc_packet),
    .o(r_input_selected_vc)
);

mux #(
    .N(2),
    .W(A_W+D_W+1)
) u0_input_mux (
    .s(u0_input_which_vc),
    .i(u0_input_vc_packet),
    .o(u0_input_selected_vc)
);

mux #(
    .N(2),
    .W(A_W+D_W+1)
) u1_input_mux (
    .s(u1_input_which_vc),
    .i(u1_input_vc_packet),
    .o(u1_input_selected_vc)
);

/* ------------------------------------------------------------------------------------------------
 * Output Muxes (Muxing the output from one of the input DIRECTIONS (not VCs))
 * --------------------------------------------------------------------------------------------- */

mux #(
    .N(3),
    .W(A_W+D_W+1)
) l_output_mux (
    .s(l_output_which_dir),
    .i({u1_input_selected_vc, u0_input_selected_vc, r_input_selected_vc}),
    .o(l_output_packet)
);

mux #(
    .N(3),
    .W(A_W+D_W+1)
) r_output_mux (
    .s(r_output_which_dir),
    .i({u1_input_selected_vc, u0_input_selected_vc, l_input_selected_vc}),
    .o(r_output_packet)
);

mux #(
    .N(2),
    .W(A_W+D_W+1)
) u0_output_mux (
    .s(u0_output_which_dir),
    .i({r_input_selected_vc, l_input_selected_vc}),
    .o(u0_output_packet)
);

mux #(
    .N(2),
    .W(A_W+D_W+1)
) u1_output_mux (
    .s(u1_output_which_dir),
    .i({r_input_selected_vc, l_input_selected_vc}),
    .o(u1_output_packet)
);

endmodule : experiment_hier_mux_pi
