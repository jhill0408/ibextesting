/*
 * File:    verif_pkg.sv
 * Brief:   Common package for non-synthesizable things :)
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

package verif_pkg;
//verilator lint_save
//verilator lint_off UNUSEDPARAM

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Derived Parameters
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Enums
 * --------------------------------------------------------------------------------------------- */

typedef enum int {
    TRAFFIC_TYPE_SYNTHETIC,
    TRAFFIC_TYPE_TRACE,
    TRAFFIC_TYPE_RX_ONLY
} traffic_type_e;

typedef enum int {
    SYNTHETIC_CMD_DONT_CARE,//For if the traffic type isn't synthetic
    SYNTHETIC_CMD_RANDOM,
    SYNTHETIC_CMD_RANDOM_LOCAL,
    SYNTHETIC_CMD_RANDOM_BITREV,
    SYNTHETIC_CMD_RANDOM_TORNADO
    //TODO other synthetic cmds from the old code
} synthetic_cmd_e;

/* ------------------------------------------------------------------------------------------------
 * Structs
 * --------------------------------------------------------------------------------------------- */

//TODO
typedef struct packed {
    logic [2:0] unused;
    logic       stop_bit;
    logic [3:0] vc;
    logic [7:0] dest_pe_addr;
} trace_entry_s;

//verilator lint_restore
endpackage : verif_pkg
