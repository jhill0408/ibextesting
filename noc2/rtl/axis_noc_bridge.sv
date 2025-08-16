/*
 * File:    axis_noc_bridge.sv
 * Brief:   Bridge between AXI Stream and the NoC's credit interface
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

module axis_noc_bridge
    import common_pkg::*;
(
    //Clock and reset
    input logic         clk,
    input logic         rst,

    //AXI Stream ports to/from PE
    axis_if.transmitter axis_req_tx,
    axis_if.transmitter axis_reply_tx,
    axis_if.receiver    axis_req_rx,
    axis_if.receiver    axis_reply_rx,

    //NoC ports
    noc_if.transmitter  noc_tx,
    noc_if.receiver     noc_rx
);

/* ------------------------------------------------------------------------------------------------
 * TODO
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

//TODO

endmodule : axis_noc_bridge
