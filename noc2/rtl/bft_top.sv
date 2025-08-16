/*
 * File:    bft_top.sv
 * Brief:   Parameterizable BFT top module
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

module bft_top
    import common_pkg::*;
#(
    parameter bft_type_e        TYPE,
    parameter bft_topology_e    TOPOLOGY,
    parameter int               NUM_CHANNELS,//VCs or physical channels depending on the type
    parameter int               NUM_CLIENTS,
    parameter int               ADDITIONAL_LATENCY = 0,//Can help with timing depending on the BFT type
    //VCs or physical channels depending on the type
    parameter int               DATA_WIDTH,
    parameter int               FIFO_DEPTH,//If applicable; depends on the BFT type
    parameter int               FAIR_CHANNEL_ARB = 0,//Can help improve latency for VC-based BFTs
) (
);


endmodule : bft_top
