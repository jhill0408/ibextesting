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
    import common_pkg::*;
#(
    parameter bft_type_e    BFT_TYPE    = BFT_TYPE_CREDITS,
    parameter int           VC_W        = DEFAULT_VC_W,//Number of virtual channels (one bit per VC, not $clog2)
    parameter int           A_W         = DEFAULT_A_W,//Address width
    parameter int           D_W         = DEFAULT_D_W
) (
    //Global signals
    input logic clk,
    input logic rst
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
} credit_noc_payload_s;

typedef struct packed {//MUST BE PACKED so this is synthesizable!
    //The noc_routeinfo_s contains routing information for the routing logic
    //to consume, OTHER THAN VIRTUAL CHANNEL NUMBERS since those are also
    //important for backpressure (and thus made seperate).
    //The routers do need to route to corresponding VCs, but the VC numbers
    //don't go into RX fifos/etc for example like addresses would.
    logic [A_W-1:0] addr;
} credit_noc_routeinfo_s;

typedef struct packed {//MUST BE PACKED so this is synthesizable!
    //Combines the noc_payload_s and noc_routeinfo_s. This includes everything that
    //can simply be lumped into the RX FIFOs/noc_pipe datapath and isn't used for backpressure.
    credit_noc_payload_s   payload;
    credit_noc_routeinfo_s routeinfo;
} credit_noc_packet_s;

//TODO structs for backpressure and deflection nocs

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//NOTE: Only one set of these signals should be used at a time (depending on TYPE)

//Credit: Transmitter -> Receiver
logic [VC_W-1:0]    credit_vc_target;//One hot to indicate VC, or 0 to not send payload
credit_noc_packet_s credit_packet;//No signals in here should matter for backpressure purposes

//Credit: Receiver -> Transmitter
logic [VC_W-1:0]    credit_vc_credit_gnt;//One hot to grant credit for VC, or 0 to not grant
//Technically it would be okay if the above was more than one-hot if the other side
//could give multiple credits at once, but this isn't realy necessary here

//Backpressure: Transmitter -> Receiver
//TODO

//Backpressure: Receiver -> Transmitter
//TODO

//Deflection: Transmitter -> Receiver
//TODO

//Deflection: Receiver -> Transmitter
//TODO

/* ------------------------------------------------------------------------------------------------
 * Modports
 * --------------------------------------------------------------------------------------------- */

modport transmitter (
    //Credit: Transmitter -> Receiver
    output credit_vc_target,
    output credit_packet,

    //Credit: Receiver -> Transmitter
    input credit_vc_credit_gnt

    //Backpressure: Transmitter -> Receiver
    //TODO

    //Backpressure: Receiver -> Transmitter
    //TODO

    //Deflection: Transmitter -> Receiver
    //TODO

    //Deflection: Receiver -> Transmitter
    //TODO
);

modport receiver (
    //Transmitter -> Receiver
    input credit_vc_target,
    input credit_packet,

    //Receiver -> Transmitter
    output credit_vc_credit_gnt

    //Backpressure: Transmitter -> Receiver
    //TODO

    //Backpressure: Receiver -> Transmitter
    //TODO

    //Deflection: Transmitter -> Receiver
    //TODO

    //Deflection: Receiver -> Transmitter
    //TODO
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

generate
if (BFT_TYPE == BFT_TYPE_CREDITS) begin : gen_credit_assertions
    //Backpressure signals shouldn't be unknown outside of reset
    assert property (@(posedge clk) disable iff (rst) !$isunknown(credit_vc_target));
    assert property (@(posedge clk) disable iff (rst) !$isunknown(credit_vc_credit_gnt));

    //Backpressure signals are one-hot or 0
    assert property (@(posedge clk) disable iff (rst) $onehot0(credit_vc_target));
    //Actually, we could technically send two credits in the same CC and that would be fine
    //assert property (@(posedge clk) disable iff (rst) $onehot0(vc_credit_gnt));

    //When a VC is being targeted, signals shouldn't be unknown
    assert property (@(posedge clk) disable iff (rst) (|credit_vc_target |-> !$isunknown(credit_packet)));
end : gen_credit_assertions
else if (BFT_TYPE == BFT_TYPE_BACKPRESSURE) begin : gen_backpressure_assertions
    //TODO
end : gen_backpressure_assertions
else if (BFT_TYPE == BFT_TYPE_DEFLECTION) begin : gen_deflection_assertions
    //TODO
end : gen_deflection_assertions
endgenerate

`endif //SIMULATION

endinterface : noc_if
