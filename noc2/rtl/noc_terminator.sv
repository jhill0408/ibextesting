/*
 * File:    noc_terminator.sv
 * Brief:   Ties off and ignores the relevant signals of an unused pair of noc_if
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

module noc_terminator
    import common_pkg::*;
#(
    parameter bft_type_e    BFT_TYPE    = BFT_TYPE_CREDITS
    /*
    parameter int           VC_W        = DEFAULT_VC_W,//Number of virtual channels (one bit per VC, not $clog2)
    parameter int           A_W         = DEFAULT_A_W,//Address width
    parameter int           D_W         = DEFAULT_D_W
    */
) (
    //Connections to the NoC
    noc_if.transmitter  to_rx,
    noc_if.receiver     from_tx
);

generate
if (BFT_TYPE == BFT_TYPE_CREDITS) begin : gen_credit_terminator
    assign to_rx.credit_vc_target       = '0;
    assign to_rx.credit_packet          = '0;
    assign from_tx.credit_vc_credit_gnt = '0;
end : gen_credit_terminator
else if (BFT_TYPE == BFT_TYPE_BACKPRESSURE) begin : gen_backpressure_terminator
    //TODO
end : gen_backpressure_terminator
else if (BFT_TYPE == BFT_TYPE_DEFLECTION) begin : gen_deflection_terminator
    //TODO
end : gen_deflection_terminator
endgenerate

endmodule : noc_terminator
