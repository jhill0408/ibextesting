/*
 * File:    topology_t_binary_tree.sv
 * Brief:   Parameterized pure-t-switch binary tree topology
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * This is analogous to BFT0 from the original paper
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module topology_t_binary_tree
    import common_pkg::*;
#(
    parameter N                 = DEFAULT_N,            //MUST BE A POWER OF 2
    parameter INTERFACE_FLOPS   = 0,                    //Number of flops between interfaces, useful to improve timing
    parameter VC_W              = DEFAULT_VC_W,
    parameter D_W               = DEFAULT_D_W,
    parameter VC_FIFO_DEPTH     = DEFAULT_VC_FIFO_DEPTH,//Actual depth is this - 1
    parameter FAIR_VC_ARB       = 0
) (
    //Clock and reset
    input logic clk,    // clock
    input logic rst,    // reset
    
    //Root port (above the uppermost flops)
    noc_if.receiver     root_rx,
    noc_if.transmitter  root_tx,
    
    //Leaf ports (below the leaf flops)
    noc_if.receiver     leaf_rx [N-1:0],
    noc_if.transmitter  leaf_tx [N-1:0]
);

/* ------------------------------------------------------------------------------------------------
 * Helpers
 * --------------------------------------------------------------------------------------------- */

localparam A_W = $clog2(N) + 1;

localparam LEVELS = $clog2(N);
`define num_switches_in_level(level) (2 ** (LEVELS - level - 1))

/* ------------------------------------------------------------------------------------------------
 * Binary Tree Topology
 * --------------------------------------------------------------------------------------------- */

//In general:
// - "upwards" vs "downwards" refers to the direction of the data flow (opposite to credit flow)
// - "below flops" vs "above flops" means physically which side of the noc_pipe the interface is refering to
//
//Think of noc_pipes as being vertical between the levels, with "below" and "above" being the physical
//location of an interface, and "upwards" and "downwards" effectively flipping the orientation of the
//noc_pipe (while leaving the interfaces alone)

// Define flat arrays for level connections
// Calculate the maximum number of switches at any level
localparam MAX_SWITCHES = 2 ** (LEVELS - 1);
localparam TOTAL_CONNECTIONS = MAX_SWITCHES * 4; // 4 connections per switch (l_rx, l_tx, r_rx, r_tx)

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W),
    .D_W(D_W)
) level_connections_flat [TOTAL_CONNECTIONS-1:0] (
    .*
);

//Leaf ports after dealing with flops as appropriate
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W),
    .D_W(D_W)
) leaf_rx_above_flops [N-1:0] (
    .*
);

noc_if #(
    .VC_W(VC_W),
    .A_W(A_W),
    .D_W(D_W)
) leaf_tx_above_flops [N-1:0] (
    .*
);

generate
for (genvar ii = 0; ii < LEVELS; ++ii) begin : gen_levels
    //Interfaces between levels
    noc_if #(
        .VC_W(VC_W),
        .A_W(A_W),
        .D_W(D_W)
    ) upwards_if_below_flops [`num_switches_in_level(ii)-1:0] (
        .*
    );

    noc_if #(
        .VC_W(VC_W),
        .A_W(A_W),
        .D_W(D_W)
    ) upwards_if_above_flops [`num_switches_in_level(ii)-1:0] (
        .*
    );

    noc_if #(
        .VC_W(VC_W),
        .A_W(A_W),
        .D_W(D_W)
    ) downwards_if_above_flops [`num_switches_in_level(ii)-1:0] (
        .*
    );

    noc_if #(
        .VC_W(VC_W),
        .A_W(A_W),
        .D_W(D_W)
    ) downwards_if_below_flops [`num_switches_in_level(ii)-1:0] (
        .*
    );

    //Generation of flops between levels for better timing
    for (genvar jj = 0; jj < `num_switches_in_level(ii); ++jj) begin : gen_flops
        noc_pipe #(
            .VC_W(VC_W),
            .A_W(A_W),
            .D_W(D_W),
            .LATENCY(INTERFACE_FLOPS)
        ) upwards_pipe (
            .*,
            .from_tx(upwards_if_below_flops[jj]),
            .to_rx(  upwards_if_above_flops[jj])
        );

        noc_pipe #(
            .VC_W(VC_W),
            .A_W(A_W),
            .D_W(D_W),
            .LATENCY(INTERFACE_FLOPS)
        ) downwards_pipe (
            .*,
            .from_tx(downwards_if_above_flops[jj]),
            .to_rx(  downwards_if_below_flops[jj])
        );
    end : gen_flops

    //Generation of switches in a level
    if (ii == 0) begin : gen_almost_leaves
        //The "Almost leave" T switches are special since their left and right ports are connected to the leaf ports
        for (genvar jj = 0; jj < `num_switches_in_level(ii); ++jj) begin : gen_almost_leaves_loop
            t_switch_top #(
                .N(N),
                .A_W(A_W),
                .D_W(D_W),
                .posl(ii),
                .posx(jj),
                .VC_W(VC_W),
                .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
                .FAIR_VC_ARB(FAIR_VC_ARB)
            ) almost_leaf_t_switch_inst (
                .clk(clk),
                .rst(rst),

                //Reach into the leaf ports to access the correct interfaces
                .l_rx(leaf_rx_above_flops[jj * 2]),
                .l_tx(leaf_tx_above_flops[jj * 2]),

                .r_rx(leaf_rx_above_flops[jj * 2 + 1]),
                .r_tx(leaf_tx_above_flops[jj * 2 + 1]),

                .u0_rx(downwards_if_below_flops[jj]),
                .u0_tx(  upwards_if_below_flops[jj])
            );
        end : gen_almost_leaves_loop
    end else begin : gen_higher_levels
        //The rest connect to the switches above and below (execpt the root port, but we deal with that later)
        for (genvar jj = 0; jj < `num_switches_in_level(ii); ++jj) begin : gen_higher_levels_loop
           // Calculate base index for this switch's connections
            localparam int base_idx = ((2**ii) - 1 + jj) * 4;
            
            // Calculate indices for the children
            localparam int left_child_idx = jj * 2;
            localparam int right_child_idx = jj * 2 + 1;
            
            // UPWARDS PATHS (RX) - FROM CHILDREN TO PARENT
            // Left child upwards
            assign level_connections_flat[base_idx + 0].vc_target = gen_levels[ii - 1].upwards_if_above_flops[left_child_idx].vc_target;
            assign level_connections_flat[base_idx + 0].packet = gen_levels[ii - 1].upwards_if_above_flops[left_child_idx].packet;
            assign gen_levels[ii - 1].upwards_if_above_flops[left_child_idx].vc_credit_gnt = level_connections_flat[base_idx + 0].vc_credit_gnt;
            
            // Right child upwards
            assign level_connections_flat[base_idx + 1].vc_target = gen_levels[ii - 1].upwards_if_above_flops[right_child_idx].vc_target;
            assign level_connections_flat[base_idx + 1].packet = gen_levels[ii - 1].upwards_if_above_flops[right_child_idx].packet;
            assign gen_levels[ii - 1].upwards_if_above_flops[right_child_idx].vc_credit_gnt = level_connections_flat[base_idx + 1].vc_credit_gnt;
            
            // DOWNWARDS PATHS (TX) - FROM PARENT TO CHILDREN
            // Left child downwards
            assign gen_levels[ii - 1].downwards_if_above_flops[left_child_idx].vc_target = level_connections_flat[base_idx + 2].vc_target;
            assign gen_levels[ii - 1].downwards_if_above_flops[left_child_idx].packet = level_connections_flat[base_idx + 2].packet;
            assign level_connections_flat[base_idx + 2].vc_credit_gnt = gen_levels[ii - 1].downwards_if_above_flops[left_child_idx].vc_credit_gnt;
            
            // Right child downwards
            assign gen_levels[ii - 1].downwards_if_above_flops[right_child_idx].vc_target = level_connections_flat[base_idx + 3].vc_target;
            assign gen_levels[ii - 1].downwards_if_above_flops[right_child_idx].packet = level_connections_flat[base_idx + 3].packet;
            assign level_connections_flat[base_idx + 3].vc_credit_gnt = gen_levels[ii - 1].downwards_if_above_flops[right_child_idx].vc_credit_gnt;

            t_switch_top #(
                .N(N),
                .A_W(A_W),
                .D_W(D_W),
                .posl(ii),
                .posx(jj),
                .VC_W(VC_W),
                .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
                .FAIR_VC_ARB(FAIR_VC_ARB)
            ) higher_level_t_switch_inst (
                .clk(clk),
                .rst(rst),

                // Use the flattened connections
                .l_rx(level_connections_flat[base_idx + 0]),
                .l_tx(level_connections_flat[base_idx + 2]),
                .r_rx(level_connections_flat[base_idx + 1]),
                .r_tx(level_connections_flat[base_idx + 3]),

                .u0_rx(downwards_if_below_flops[jj]),
                .u0_tx(upwards_if_below_flops[jj])
            );
        end : gen_higher_levels_loop
    end : gen_higher_levels
end : gen_levels
endgenerate

//Connect up the root, which wasn't treated specially (so we account for that here)
assign gen_levels[LEVELS - 1].downwards_if_above_flops[0].vc_target = root_rx.vc_target;
assign gen_levels[LEVELS - 1].downwards_if_above_flops[0].packet    = root_rx.packet;
assign root_rx.vc_credit_gnt                                        = gen_levels[LEVELS - 1].downwards_if_above_flops[0].vc_credit_gnt;

assign root_tx.vc_target                                                = gen_levels[LEVELS - 1].upwards_if_above_flops[0].vc_target;
assign root_tx.packet                                                   = gen_levels[LEVELS - 1].upwards_if_above_flops[0].packet;
assign gen_levels[LEVELS - 1].upwards_if_above_flops[0].vc_credit_gnt   = root_tx.vc_credit_gnt;

//Deal with flops for leaf interfaces
generate
for (genvar ii = 0; ii < N; ++ii) begin : gen_leaf_flops
    noc_pipe #(
        .VC_W(VC_W),
        .A_W(A_W),
        .D_W(D_W),
        .LATENCY(INTERFACE_FLOPS)
    ) leaf_rx_pipe (
        .*,
        .from_tx(leaf_rx[ii]),
        .to_rx(leaf_rx_above_flops[ii])
    );

    noc_pipe #(
        .VC_W(VC_W),
        .A_W(A_W),
        .D_W(D_W),
        .LATENCY(INTERFACE_FLOPS)
    ) leaf_tx_pipe (
        .clk(clk),
        .rst(rst),
        .from_tx(leaf_tx_above_flops[ii]),
        .to_rx(leaf_tx[ii])
    );
end : gen_leaf_flops
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

//`ifdef SIMULATION

initial begin
    //Prevent bad configuration of this module
    assert(N > 0);
    assert(VC_W > 0);
    assert(D_W > 0);
    assert(N == (2 ** $clog2(N)));
end

//`endif //SIMULATION

endmodule : topology_t_binary_tree
