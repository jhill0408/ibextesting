/*
 * File:    experiment_generic_mux6.sv
 * Brief:   FPGA mapping experiment: Comparison of parameterizable mux against Mux6
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module experiment_generic_mux6
    import common_pkg::*;
#(
    localparam N = 6,           //Number of inputs
    localparam W = DEFAULT_D_W, //Width of each input and the output
    localparam L = $clog2(N)    //Number of select lines
) (
    input  logic        [L-1:0] s,
    input  logic [N-1:0][W-1:0] i,
    output logic        [W-1:0] o
);

mux #(.N(N), .W(W)) mux_inst (.*);

endmodule : experiment_generic_mux6
