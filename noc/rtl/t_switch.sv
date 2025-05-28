/*
 * File:    t_switch.sv
 * Brief:   Routing decision logic + direction muxes
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

module t_switch
    import common_pkg::*;
#(
    parameter N             = DEFAULT_N,    // number of clients
    parameter A_W           = DEFAULT_A_W,  // log number of clients ($clog2(N) + 1)
    parameter D_W           = DEFAULT_D_W,
    parameter posl          = 0,            // Vertical position in the NoC
    parameter posx          = 0,            // Horizontal position in the level
    parameter VC_W          = DEFAULT_VC_W,
    parameter FAIR_VC_ARB   = 0             //Whether to use static VC prioritization or matrix arbiters
) (
    //Clock and reset
    input logic clk,    // clock
    input logic rst,    // reset

    //Reminder that there's multiple inputs from each direction (since there's
    //one FIFO per direction) but only singular outputs for each direction
    //since output arbitration isn't abstracted away since we need control)

    //Left input
    input  logic [VC_W-1:0][A_W+D_W:0]  l_i,    // left  input
    output logic [VC_W-1:0]             l_i_bp, // left  input backpressured
    input  logic [VC_W-1:0]             l_i_v,  // left  input valid

    //Right input
    input  logic [VC_W-1:0][A_W+D_W:0]  r_i,    // right input payload
    output logic [VC_W-1:0]             r_i_bp, // right input backpressured
    input  logic [VC_W-1:0]             r_i_v,  // right input valid
    
    //Up0 input
    input  logic [VC_W-1:0][A_W+D_W:0]  u0_i,   // u0    input payload
    output logic [VC_W-1:0]             u0_i_bp,// u0    input backpressured
    input  logic [VC_W-1:0]             u0_i_v, // u0    input valid

    //Left output
    output logic [A_W+D_W:0]    l_o,    // left  output payload
    input  logic [VC_W-1:0]     l_o_bp, // left  output backpressured
    output logic [VC_W-1:0]     l_o_v,  // left  output valid

    //Right output
    output logic [A_W+D_W:0]    r_o,    // right output payload
    input  logic [VC_W-1:0]     r_o_bp, // right output backpressured
    output logic [VC_W-1:0]     r_o_v,  // right output valid

    //Up0 output
    output logic [A_W+D_W:0]    u0_o,   // u0    output payload
    input  logic [VC_W-1:0]     u0_o_bp,// u0    output backpressured
    output logic [VC_W-1:0]     u0_o_v  // u0    output valid
);

/* ------------------------------------------------------------------------------------------------
 * Internal Signals
 * --------------------------------------------------------------------------------------------- */

//Addresses from packet inputs
logic [VC_W-1:0][A_W-1:0]  l_i_addr;
logic [VC_W-1:0][A_W-1:0]  r_i_addr;
logic [VC_W-1:0][A_W-1:0] u0_i_addr;

//Multiplexer selects
//Each half of the possible outputs indicates different VCs from the same input direction
logic [$clog2(VC_W*2)-1:0]  l_sel;
logic [$clog2(VC_W*2)-1:0]  r_sel;
logic [$clog2(VC_W*2)-1:0] u0_sel;

/* ------------------------------------------------------------------------------------------------
 * Address Breakout
 * --------------------------------------------------------------------------------------------- */

generate
for (genvar ii = 0; ii < VC_W; ++ii) begin : gen_addr_breakout
    assign  l_i_addr[ii] =  l_i[ii][A_W+D_W-1:D_W];
    assign  r_i_addr[ii] =  r_i[ii][A_W+D_W-1:D_W];
    assign u0_i_addr[ii] = u0_i[ii][A_W+D_W-1:D_W];
end : gen_addr_breakout
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Routing and Muxing
 * --------------------------------------------------------------------------------------------- */

t_route #(
    .N(N),
    .A_W(A_W),
    .posx(posx),
    .posl(posl),
    .VC_W(VC_W),
    .FAIR_VC_ARB(FAIR_VC_ARB)
) t_route_inst ( 
    .clk        (clk      ), 
    .rst        (rst      ), 
    .l_i_v      (l_i_v    ),
    .l_i_bp     (l_i_bp   ),
    .l_i_addr   (l_i_addr ),
    .r_i_v      (r_i_v    ),
    .r_i_bp     (r_i_bp   ),
    .r_i_addr   (r_i_addr ),
    .u0_i_v     (u0_i_v   ),
    .u0_i_bp    (u0_i_bp  ),
    .u0_i_addr  (u0_i_addr),
    .l_o_v      (l_o_v    ), 
    .r_o_v      (r_o_v    ), 
    .u0_o_v     (u0_o_v   ), 
    .l_o_bp     (l_o_bp   ), 
    .r_o_bp     (r_o_bp   ), 
    .u0_o_bp    (u0_o_bp  ), 
    .l_sel      (l_sel    ),
    .r_sel      (r_sel    ),
    .u0_sel     (u0_sel   )
);

mux #(
    .N(VC_W*2),//We need one mux input per VC per direction
    .W(A_W+D_W+1)
) l_mux (
    .s(l_sel),
    .i({r_i, u0_i}),
    .o(l_o)
);

mux #(
    .N(VC_W*2),
    .W(A_W+D_W+1)
) r_mux (
    .s(r_sel),
    .i({l_i, u0_i}),
    .o(r_o)
);

mux #(
    .N(VC_W*2),
    .W(A_W+D_W+1)
) u0_mux (
    .s(u0_sel),
    .i({l_i, r_i}),
    .o(u0_o)
);

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

`endif //SIMULATION

endmodule : t_switch
