/*
 * File:    topology_pi_rectangle.sv
 * Brief:   Parameterized pure-t-switch binary tree topology
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * This is analogous to BFT3 from the original paper
 *
 * Useful: Figure 10-10 from Parallel Computer Architecture:
 * A Hardware/Software Approach by David Culler, Jaswinder Pal Singh,
 * Anoop Gupta
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module topology_pi_rectangle
    import common_pkg::*;
#(
    parameter N                 = DEFAULT_N,            //MUST BE A POWER OF 2
    parameter INTERFACE_FLOPS   = 0,                    //Number of flops between interfaces, useful to improve timing
    parameter VC_W              = DEFAULT_VC_W,
    parameter D_W               = DEFAULT_D_W,
    parameter VC_FIFO_DEPTH     = DEFAULT_VC_FIFO_DEPTH,//Actual depth is this - 1
    parameter FAIR_VC_ARB       = 0,
    parameter GENERALIZED       = 0
) (
    //Clock and reset
    input logic clk,
    input logic rst,
    
    //Root ports (above the uppermost flops)
    noc_if.receiver     root_rx [N-1:0],
    noc_if.transmitter  root_tx [N-1:0],
    
    //Leaf ports (below the leaf flops)
    noc_if.receiver     leaf_rx [N-1:0],
    noc_if.transmitter  leaf_tx [N-1:0]
);

/* ------------------------------------------------------------------------------------------------
 * Derived Parameters
 * --------------------------------------------------------------------------------------------- */

//There are log2(N) levels and N/2 switches in each level

localparam A_W                  = $clog2(N) + 1;
localparam LEVELS               = $clog2(N);
localparam SWITCHES_PER_LEVEL   = N / 2;

//Groups refer to groups of switches, not interfaces
`define groups_in_level(level)      (SWITCHES_PER_LEVEL / (2 ** level))
`define group_size_at_level(level)  (2 ** level)

/* ------------------------------------------------------------------------------------------------
 * Rectangular Pi Topology
 * --------------------------------------------------------------------------------------------- */

//In general:
// - "upwards" vs "downwards" refers to the direction of the data flow (opposite to credit flow)
// - "below flops" vs "above flops" means physically which side of the noc_pipe the interface is refering to
//
//Think of noc_pipes as being vertical between the levels, with "below" and "above" being the physical
//location of an interface, and "upwards" and "downwards" effectively flipping the orientation of the
//noc_pipe (while leaving the interfaces alone)

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
    ) upwards_if_above_flops [N-1:0] (
        .*
    );

    noc_if #(
        .VC_W(VC_W),
        .A_W(A_W),
        .D_W(D_W)
    ) upwards_if_below_flops [N-1:0] (
        .*
    );

    noc_if #(
        .VC_W(VC_W),
        .A_W(A_W),
        .D_W(D_W)
    ) downwards_if_above_flops [N-1:0] (
        .*
    );

    noc_if #(
        .VC_W(VC_W),
        .A_W(A_W),
        .D_W(D_W)
    ) downwards_if_below_flops [N-1:0] (
        .*
    );

    //Generation of flops between levels for better timing
    for (genvar jj = 0; jj < N; ++jj) begin : gen_flops
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
        //The "Almost leave" Pi switches are special since their left and right ports are connected to the leaf ports
        for (genvar jj = 0; jj < SWITCHES_PER_LEVEL; ++jj) begin : gen_almost_leaves_loop
            pi_switch_top #(
                .N(N),
                .A_W(A_W),
                .D_W(D_W),
                .posl(ii),
                .posx(jj),
                .VC_W(VC_W),
                .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
                .FAIR_VC_ARB(FAIR_VC_ARB),
                .GENERALIZED(GENERALIZED)
            ) almost_leaf_pi_switch_inst (
                .clk(clk),
                .rst(rst),

                //Reach into the leaf ports to access the correct interfaces
                .l_rx(leaf_rx_above_flops[jj * 2]),
                .l_tx(leaf_tx_above_flops[jj * 2]),

                .r_rx(leaf_rx_above_flops[jj * 2 + 1]),
                .r_tx(leaf_tx_above_flops[jj * 2 + 1]),

                .u0_rx(downwards_if_below_flops[jj * 2]),
                .u0_tx(  upwards_if_below_flops[jj * 2]),

                .u1_rx(downwards_if_below_flops[jj * 2 + 1]),
                .u1_tx(  upwards_if_below_flops[jj * 2 + 1])
            );
        end : gen_almost_leaves_loop
    end else begin : gen_higher_levels
        //The rest connect to the switches above and below (execpt the root ports, but we deal with that later)

        //Groups refer to groups of switches, not interfaces
        //I'll be explicit about groups of interfaces as if_ groups
        for (genvar jj = 0; jj < `groups_in_level(ii); ++jj) begin : gen_higher_level_groups_loop
            localparam group_size = `group_size_at_level(ii);
            localparam group_base = jj * group_size;

            //There are twice as many interfaces at a given level as there are switches
            localparam if_group_base    = group_base * 2;
            localparam num_ifs_in_group = group_size * 2;

            for (genvar kk = 0; kk < group_size; ++kk) begin : gen_higher_levels_loop
                //Absolute SWITCH position
                localparam abs_posx = group_base + kk;

                //The left half of the group has the same index for the left
                //and u0 interfaces. Similiarly, the right half of the group
                //has the same index for the right and u1 interfaces
                //Otherwise, the left/right interfaces skip ahead to the other
                //side in order to realize the butterfly pattern
                localparam half_group_size  = group_size / 2;
                localparam half_num_ifs     = num_ifs_in_group / 2;

                localparam left_if_offset   = (kk < half_group_size) ? 0                : -half_num_ifs + 1;
                localparam right_if_offset  = (kk < half_group_size) ? half_num_ifs - 1 : 0;

                localparam l_idx    = if_group_base + (kk * 2) + left_if_offset;
                localparam u0_idx   = if_group_base + (kk * 2);
                localparam r_idx    = if_group_base + (kk * 2) + 1 + right_if_offset;
                localparam u1_idx   = if_group_base + (kk * 2) + 1;

                pi_switch_top #(
                    .N(N),
                    .A_W(A_W),
                    .D_W(D_W),
                    .posl(ii),
                    .posx(jj),//The effective "posx" is the group number
                    .VC_W(VC_W),
                    .VC_FIFO_DEPTH(VC_FIFO_DEPTH),
                    .FAIR_VC_ARB(FAIR_VC_ARB),
                    .GENERALIZED(GENERALIZED)
                ) higher_level_pi_switch_inst (
                    .clk(clk),
                    .rst(rst),

                    .l_rx(gen_levels[ii - 1].  upwards_if_above_flops[l_idx]),
                    .l_tx(gen_levels[ii - 1].downwards_if_above_flops[l_idx]),

                    .r_rx(gen_levels[ii - 1].  upwards_if_above_flops[r_idx]),
                    .r_tx(gen_levels[ii - 1].downwards_if_above_flops[r_idx]),

                    .u0_rx(downwards_if_below_flops[u0_idx]),
                    .u0_tx(  upwards_if_below_flops[u0_idx]),

                    .u1_rx(downwards_if_below_flops[u1_idx]),
                    .u1_tx(  upwards_if_below_flops[u1_idx])
                );
            end : gen_higher_levels_loop
        end : gen_higher_level_groups_loop
    end : gen_higher_levels
end : gen_levels
endgenerate

//Connect up the roots, which weren't treated specially (so we account for that here)
generate
for (genvar ii = 0; ii < N; ++ii) begin : gen_root
    assign gen_levels[LEVELS - 1].downwards_if_above_flops[ii].vc_target    = root_rx[ii].vc_target;
    assign gen_levels[LEVELS - 1].downwards_if_above_flops[ii].packet       = root_rx[ii].packet;
    assign root_rx[ii].vc_credit_gnt                                        = gen_levels[LEVELS - 1].downwards_if_above_flops[ii].vc_credit_gnt;

    assign root_tx[ii].vc_target                                            = gen_levels[LEVELS - 1].upwards_if_above_flops[ii].vc_target;
    assign root_tx[ii].packet                                               = gen_levels[LEVELS - 1].upwards_if_above_flops[ii].packet;
    assign gen_levels[LEVELS - 1].upwards_if_above_flops[ii].vc_credit_gnt  = root_tx[ii].vc_credit_gnt;
end : gen_root
endgenerate

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
        .from_tx(leaf_rx            [ii]),
        .to_rx(  leaf_rx_above_flops[ii])
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
        .to_rx(  leaf_tx            [ii])
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

endmodule : topology_pi_rectangle
