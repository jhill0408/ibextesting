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

parameter int DEFAULT_VC_FIFO_DEPTH = 64;//Number of fifo entries + 1; should be multiple of 32

/* ------------------------------------------------------------------------------------------------
 * Derived Parameters
 * --------------------------------------------------------------------------------------------- */

parameter int DEFAULT_TSTRB_W = DEFAULT_TDATA_W / 8;
parameter int DEFAULT_TKEEP_W = DEFAULT_TDATA_W / 8;

parameter int DEFAULT_VC_COUNTER_W = $clog2(DEFAULT_VC_FIFO_DEPTH);

/* ------------------------------------------------------------------------------------------------
 * Structs
 * --------------------------------------------------------------------------------------------- */

//DEPRECATED: Use noc_if directly instead (since raw structs don't support
//heterogenous parameterization (if you wanted different A_Ws for example inwithout modifying common_pkg))

typedef struct packed {//MUST BE PACKED so this is synthesizable!
    //The noc_payload_s will not contain ANYTHING needed for routing information or backpressure
    //For now it just contains data and last, though if it ends up helping the AXIS <-> noc_if bridges
    //to have other signals we could add them here.
    //TODO would we need to paramaterize the payload to be different than the defaults? If so we can't use a struct...
    logic [DEFAULT_D_W-1:0] data;
    logic                   last;
} noc_payload_s;
parameter int NOC_PAYLOAD_W = $bits(noc_payload_s);

typedef struct packed {//MUST BE PACKED so this is synthesizable!
    //The noc_routeinfo_s contains routing information for the routing logic
    //to consume, OTHER THAN VIRTUAL CHANNEL NUMBERS since those are also
    //important for backpressure (and thus made seperate).
    //The routers do need to route to corresponding VCs, but the VC numbers
    //don't go into RX fifos/etc for example like addresses would.
    //TODO would we need to paramaterize this to be different than the defaults? If so we can't use a struct...
    logic [DEFAULT_A_W-1:0] addr;
} noc_routeinfo_s;
parameter int NOC_ROUTEINFO_W = $bits(noc_routeinfo_s);

typedef struct packed {//MUST BE PACKED so this is synthesizable!
    //Combines the noc_payload_s and noc_routeinfo_s. This includes everything that
    //can simply be lumped into the RX FIFOs/noc_pipe datapath and isn't used for backpressure.
    noc_payload_s   payload;
    noc_routeinfo_s routeinfo;
} noc_packet_s;
parameter int NOC_PACKET_W = $bits(noc_packet_s);

//verilator lint_restore
endpackage : common_pkg
