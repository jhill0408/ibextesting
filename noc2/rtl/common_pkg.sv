/*
 * File:    common_pkg.sv
 * Brief:   Common package for NoC implementation and other purposes
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Package Definition
 * --------------------------------------------------------------------------------------------- */

package common_pkg;

/* ------------------------------------------------------------------------------------------------
 * Enums
 * --------------------------------------------------------------------------------------------- */

typedef enum int {
    BFT_TYPE_CREDITS,
    BFT_TYPE_BACKPRESSURE,
    BFT_TYPE_DEFLECTION
} bft_type_e;

typedef enum int {
    BFT_TOPOLOGY_BINARY_TREE,
    //TODO others in-between
    BFT_TOPOLOGY_CROSSBAR,
    BFT_TOPOLOGY_CROSSBAR_GENERALIZED_PI
} bft_topology_e;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */



/* ------------------------------------------------------------------------------------------------
 * Derived Parameters
 * --------------------------------------------------------------------------------------------- */

//OLD parameters below

//verilator lint_save
//verilator lint_off UNUSEDPARAM

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

//TODO base these defaults off of what is provided on the simulation command line

parameter int DEFAULT_N         = 8;//Number of clients

parameter int DEFAULT_D_W       = 32;//Data width

//Default widths for noc_if, other modules if not overridden
parameter int DEFAULT_VC_W      = 2;                  //Number of virtual channels (one bit per VC, not $clog2)
parameter int DEFAULT_A_W       = $clog2(DEFAULT_N)+1;//Address width

//Default widths for axis_if, other axi-related modules if not overridden
parameter int DEFAULT_TDATA_W   = DEFAULT_D_W;
parameter int DEFAULT_TID_W     = 8;
parameter int DEFAULT_TDEST_W   = 8;//TODO what should this default to?

parameter int DEFAULT_VC_FIFO_DEPTH = 32;//Number of fifo entries + 1; should be multiple of 32

/* ------------------------------------------------------------------------------------------------
 * Derived Parameters
 * --------------------------------------------------------------------------------------------- */

parameter int DEFAULT_TSTRB_W = DEFAULT_TDATA_W / 8;
parameter int DEFAULT_TKEEP_W = DEFAULT_TDATA_W / 8;

parameter int DEFAULT_VC_COUNTER_W = $clog2(DEFAULT_VC_FIFO_DEPTH);

/* ------------------------------------------------------------------------------------------------
 * Structs
 * --------------------------------------------------------------------------------------------- */

//TODO

//verilator lint_restore
endpackage : common_pkg
