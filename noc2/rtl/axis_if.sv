/*
 * File:    axis_if.sv
 * Brief:   AXI Stream interface
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Interface Definition
 * --------------------------------------------------------------------------------------------- */

interface axis_if
    import common_pkg::*;
#(
    parameter int TDATA_W   = DEFAULT_TDATA_W,
    parameter int TID_W     = DEFAULT_TID_W,
    parameter int TDEST_W   = DEFAULT_TDEST_W
) (
    //Global signals
    input logic aclk,
    input logic arst_n
);

/* ------------------------------------------------------------------------------------------------
 * Derived Parameters
 * --------------------------------------------------------------------------------------------- */

localparam int TSTRB_W = TDATA_W / 8;
localparam int TKEEP_W = TDATA_W / 8;

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//Transmitter -> Receiver
logic               tvalid;
logic [TDATA_W-1:0] tdata;
logic [TSTRB_W-1:0] tstrb;
logic [TKEEP_W-1:0] tkeep;
logic               tlast;
logic [TID_W-1:0]   tid;
logic [TDEST_W-1:0] tdest;
logic               twakeup;

//Receiver -> Transmitter
logic tready;

/* ------------------------------------------------------------------------------------------------
 * Modports
 * --------------------------------------------------------------------------------------------- */

modport transmitter (
    //Transmitter -> Receiver
    output tvalid,
    output tdata,
    output tstrb,
    output tkeep,
    output tlast,
    output tid,
    output tdest,
    output twakeup,

    //Receiver -> Transmitter
    input tready
);

modport receiver (
    //Transmitter -> Receiver
    input tvalid,
    input tdata,
    input tstrb,
    input tkeep,
    input tlast,
    input tid,
    input tdest,
    input twakeup,

    //Receiver -> Transmitter
    output tready
);

/* ------------------------------------------------------------------------------------------------
 * Functions
 * --------------------------------------------------------------------------------------------- */

function logic transfer_complete();//At next posedge
    return tvalid & tready;
endfunction

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Parameter assertions
initial begin
    assert(TDATA_W > 0);
    assert((TDATA_W % 8) == 0);
    assert(TID_W > 0);
    assert(TDEST_W > 0);
    assert(TSTRB_W > 0);
    assert(TKEEP_W > 0);
end

//Valid and ready signals shouldn't be unknown outside of reset
assert property (@(posedge aclk) disable iff (!arst_n) !$isunknown(tvalid));
assert property (@(posedge aclk) disable iff (!arst_n) !$isunknown(tready));

//When valid, signals shouldn't be unknown
assert property (@(posedge aclk) disable iff (!arst_n) (tvalid |-> !$isunknown(tdata)));
assert property (@(posedge aclk) disable iff (!arst_n) (tvalid |-> !$isunknown(tstrb)));
assert property (@(posedge aclk) disable iff (!arst_n) (tvalid |-> !$isunknown(tkeep)));
assert property (@(posedge aclk) disable iff (!arst_n) (tvalid |-> !$isunknown(tlast)));
assert property (@(posedge aclk) disable iff (!arst_n) (tvalid |-> !$isunknown(tid)));
assert property (@(posedge aclk) disable iff (!arst_n) (tvalid |-> !$isunknown(tdest)));
assert property (@(posedge aclk) disable iff (!arst_n) (tvalid |-> !$isunknown(twakeup)));

//AXI valid and ready handshaking
`ifndef VERILATOR//Verilator doesn't support the `throughout` keyword
assert property (@(posedge aclk) disable iff (!arst_n) tvalid |-> (tvalid throughout tready[->1]));
`endif //VERILATOR

//Signals stable while valid
//TODO

//TODO others

`endif //SIMULATION

endinterface : axis_if
