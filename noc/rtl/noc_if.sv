/*
 * File:    noc_if.sv
 * Brief:   Credit-based interface for NoC implementation
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Inspired somewhat by AXI Stream, which is particularly useful to simplify
 * the NoC <-> PE bridges. Signal names were changed to avoid confusion since
 * these aren't 100% compatible.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Interface Definition
 * --------------------------------------------------------------------------------------------- */

interface noc_if
    import common_pkg::DEFAULT_VC_W;
    import common_pkg::DEFAULT_A_W;
    import common_pkg::DEFAULT_D_W;
#(
    parameter int VC_W  = DEFAULT_VC_W,//Number of virtual channels (one bit per VC, not $clog2)
    parameter int A_W   = DEFAULT_A_W,//Address width
    parameter int D_W   = DEFAULT_D_W
) (
    //Global signals
    /* verilator lint_off UNUSEDSIGNAL */
    input logic clk,
    input logic rst
    /* verilator lint_on UNUSEDSIGNAL */
);

/* ------------------------------------------------------------------------------------------------
 * Structs
 * --------------------------------------------------------------------------------------------- */

typedef struct packed {//MUST BE PACKED so this is synthesizable!
    //The noc_payload_s will not contain ANYTHING needed for routing information or backpressure
    //For now it just contains data and last, though if it ends up helping the AXIS <-> noc_if bridges
    //to have other signals we could add them here.
    logic [D_W-1:0] data;
    logic           last;
    
} noc_payload_s;

typedef struct packed {//MUST BE PACKED so this is synthesizable!
    //The noc_routeinfo_s contains routing information for the routing logic
    //to consume, OTHER THAN VIRTUAL CHANNEL NUMBERS since those are also
    //important for backpressure (and thus made seperate).
    //The routers do need to route to corresponding VCs, but the VC numbers
    //don't go into RX fifos/etc for example like addresses would.
    logic [A_W-1:0] addr;
} noc_routeinfo_s;

typedef struct packed {//MUST BE PACKED so this is synthesizable!
    //Combines the noc_payload_s and noc_routeinfo_s. This includes everything that
    //can simply be lumped into the RX FIFOs/noc_pipe datapath and isn't used for backpressure.
    noc_payload_s   payload;
    noc_routeinfo_s routeinfo;
} noc_packet_s;

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//Transmitter -> Receiver
logic [VC_W-1:0]    vc_target;//One hot to indicate VC, or 0 to not send payload
noc_packet_s        packet;//No signals in here should matter for backpressure purposes

//Receiver -> Transmitter
logic [VC_W-1:0]    vc_credit_gnt;//One hot to grant credit for VC, or 0 to not grant
//Technically it would be okay if the above was more than one-hot if the other side
//could give multiple credits at once, but this isn't realy necessary here

/* ------------------------------------------------------------------------------------------------
 * Modports
 * --------------------------------------------------------------------------------------------- */

modport transmitter (
    //Transmitter -> Receiver
    output vc_target,
    output packet,

    //Receiver -> Transmitter
    input vc_credit_gnt
);

modport receiver (
    //Transmitter -> Receiver
    input vc_target,
    input packet,

    //Receiver -> Transmitter
    output vc_credit_gnt
);

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Parameter assertions
initial begin
    assert(VC_W > 0);
    assert(A_W > 0);
end

//Backpressure signals shouldn't be unknown outside of reset
assert property (@(posedge clk) disable iff (rst) !$isunknown(vc_target));
assert property (@(posedge clk) disable iff (rst) !$isunknown(vc_credit_gnt));

//Backpressure signals are one-hot or 0
assert property (@(posedge clk) disable iff (rst) $onehot0(vc_target));
//Actually, we could technically send two credits in the same CC and that would be fine
//assert property (@(posedge clk) disable iff (rst) $onehot0(vc_credit_gnt));

//When a VC is being targeted, signals shouldn't be unknown
assert property (@(posedge clk) disable iff (rst) (|vc_target |-> !$isunknown(packet)));

`endif //SIMULATION

endinterface : noc_if
