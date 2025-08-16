/*
 * File:    mux.sv
 * Brief:   Parameterizable mux
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Confirmed to take the same number (or less) LUTs as the original hardcoded muxes
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module mux #(
    parameter  N = 2,        //Number of inputs
    parameter  W = 32,       //Width of each input and the output
    localparam L = $clog2(N) //Number of select lines
) (
    input  logic        [L-1:0] s,
    input  logic [N-1:0][W-1:0] i,
    output logic        [W-1:0] o
);

//TODO perhaps avoid these warnings in a more proper way? Ex ((L+1)'(s) < (L+1)'(N)), works but is there a hardware cost?
//verilator lint_save
//verilator lint_off WIDTH

//The check for out of bounds here actually saves LUTs in testing in both Vivado and Yosys
assign o = (s < N) ? i[s] : '0;

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Since we don't have a clock, we use an always block instead which triggers on any change of s
//assert property (@(posedge clk) disable iff (rst) s < N);

always_comb begin
    assert(s < N);
end

`endif //SIMULATION

//verilator lint_restore

endmodule : mux
