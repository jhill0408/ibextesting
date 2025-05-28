/**
 * File    credit_bp_rx_tb.sv
 * Brief   TODO
 *
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Macros
 * --------------------------------------------------------------------------------------------- */

//Due to Xsim/Verilator mismatches with clocking blocks, we concede defeat and
//have verif live on the negative edge
`define WAITN(n) repeat(n) @(negedge clk)

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module credit_bp_rx_tb;

import common_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam  CLOCK_PERIOD = 10;

localparam  VC_W  = DEFAULT_VC_W;
localparam  D_W   = DEFAULT_D_W;
localparam  A_W   = DEFAULT_A_W;
localparam  DEPTH = DEFAULT_VC_FIFO_DEPTH;//Actual depth is this - 1

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;
logic rst = 1'b1;//To ensure rst is asserted at the beginning of the sim

//Connection to the transmitter
noc_if #(
    .VC_W(VC_W),
    .A_W(A_W)
) from_tx (
    .*
);

//DVR interface to the switch routing logic
logic [VC_W-1:0]            o_v;//One valid signal per VC
logic [VC_W-1:0][A_W+D_W:0] o_d;//Data, address, and last signals are per VC//TODO update other RTL and make an array of noc_packet_s instead
logic [VC_W-1:0]            i_b;//And so too are the ready signals

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

credit_bp_rx #(
    .VC_W(VC_W),
    .D_W(D_W),
    .A_W(A_W),
    .DEPTH(DEPTH)
) dut (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

initial begin
    forever begin
        clk = 1'b0;
        #(CLOCK_PERIOD / 2);
        clk = 1'b1;
        #(CLOCK_PERIOD / 2);
    end
end

always @(posedge clk) begin
    $display(
        "t=%t rst=%b vc_target=%b packet={%h,%h,%h} vc_credit_gnt=%b o_v=%b o_d[0]={%h,%h,%h} o_d[1]={%h,%h,%h} i_b=%b",
        $time, rst, from_tx.vc_target,
        from_tx.packet.payload.data, from_tx.packet.payload.last, from_tx.packet.routeinfo.addr,
        from_tx.vc_credit_gnt, o_v,
        o_d[0][D_W-1:0], o_d[0][D_W+A_W-1:D_W], o_d[0][A_W+D_W],
        o_d[1][D_W-1:0], o_d[1][D_W+A_W-1:D_W], o_d[1][A_W+D_W],
        i_b
    );
end

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Assert reset for a couple clock cycles, and set initial inputs
    rst                 <= 1'b1;
    from_tx.vc_target   <= '0;
    from_tx.packet      <= '0;
    i_b                 <= '1;
    `WAITN(2);
    rst <= 1'b0;
    `WAITN(2);
    assert(o_v == '0);//Right after reset there shouldn't be any data in either VC fifo
    assert(from_tx.vc_credit_gnt == '0);//No data to pop so no credits to grant

    //If we disable backpressure while we don't have data, nothing should happen
    i_b <= '0;
    `WAITN(2);
    assert(o_v == '0);
    assert(from_tx.vc_credit_gnt == '0);

    //Now let's push something to VC0's fifo, while backpressuring VC1
    i_b                         <= 2'b10;
    from_tx.vc_target           <= 2'b01;
    from_tx.packet.payload.data <= 32'hDEADBEEF;
    `WAITN(1);
    i_b                 <= '0;
    from_tx.vc_target   <= '0;
    from_tx.packet      <= '0;
    assert(o_v              == 2'b01);//The data should be provided in the next cycle
    assert(o_d[0][D_W-1:0]  == 32'hDEADBEEF);//It should be correct
    assert(from_tx.vc_credit_gnt == 2'b01);//Should get a credit back since VC0 isn't backpressured
    `WAITN(1);
    assert(o_v                   == 2'b00);//The pop is done
    assert(from_tx.vc_credit_gnt == 2'b00);//No credits left to grant

    //Push again, but backpressure VC0 now
    i_b                         <= 2'b01;
    from_tx.vc_target           <= 2'b01;
    from_tx.packet.payload.data <= 32'h1234ABCD;
    `WAITN(1);
    i_b                         <= 2'b01;//Still backpressuring the VC0 fifo
    from_tx.vc_target           <= 2'b00;
    from_tx.packet.payload.data <= 32'h00000000;
    assert(o_v                   == 2'b01);//The data should be available in the next CC
    assert(o_d[0][D_W-1:0]       == 32'h1234ABCD);//It should be correct
    assert(from_tx.vc_credit_gnt == '0);//But we're backpressured so a credit shouldn't be granted

    //Take break for a few more cycles, and nothing should have changed
    `WAITN(3);
    assert(o_v                   == 2'b01);//The data should be available still
    assert(o_d[0][D_W-1:0]       == 32'h1234ABCD);//It should be correct
    assert(from_tx.vc_credit_gnt == '0);//But we're backpressured so a credit shouldn't be granted

    //Start to take it up a notch. Pop the previous payload from VC0, and push to a backpressured VC1
    i_b                         <= 2'b10;
    from_tx.vc_target           <= 2'b10;
    from_tx.packet.payload.data <= 32'hCAFEBABE;
    #(CLOCK_PERIOD / 4);//Credit granted combinationally
    assert(o_v                   == 2'b01);//The VC0 data should be available still since a pop takes a CC
    assert(o_d[0][D_W-1:0]       == 32'h1234ABCD);//It should be correct
    assert(from_tx.vc_credit_gnt == 2'b01);//But we should have a credit for VC0 now!
    `WAITN(1);
    assert(o_v                   == 2'b10);//VC1 data should be in the FIFO now
    assert(o_d[1][D_W-1:0]       == 32'hCAFEBABE);//We should also see the VC1 data
    assert(from_tx.vc_credit_gnt == 2'b00);//But no credits since VC1 is backpressured!
    from_tx.packet.payload.data  <= 32'h22222222;//Push another thing to VC1 back-to-back
    `WAITN(1);
    assert(o_v                   == 2'b10);//VC0's still empty, VC1 should still have data
    assert(o_d[1][D_W-1:0]       == 32'hCAFEBABE);//It shouldn't have changed
    assert(from_tx.vc_credit_gnt == '0);//No credits for us
    i_b                          <= 2'b11;
    from_tx.vc_target            <= 2'b01;
    from_tx.packet.payload.data  <= 32'h33333333;//Now let's push to VC0 back-to-back after VC1
    `WAITN(1);
    assert(o_v                   == 2'b11);//Both have data now!
    assert(o_d[0][D_W-1:0]       == 32'h33333333);
    assert(o_d[1][D_W-1:0]       == 32'hCAFEBABE);//Still ORIGINAL VC1 data
    assert(from_tx.vc_credit_gnt == '0);//No credits for us
    i_b                          <= 2'b01;//Pop VC1
    from_tx.vc_target            <= '0;
    from_tx.packet.payload.data  <= '0;
    #(CLOCK_PERIOD / 4);//Credit granted combinationally
    //Everything is the same as before the updated inputs EXCEPT the credits!
    assert(o_v                   == 2'b11);
    assert(o_d[0][D_W-1:0]       == 32'h33333333);
    assert(o_d[1][D_W-1:0]       == 32'hCAFEBABE);
    assert(from_tx.vc_credit_gnt == 2'b10);//Thanks VC1!
    `WAITN(1);
    assert(o_v                   == 2'b11);//Both still have data!
    assert(o_d[0][D_W-1:0]       == 32'h33333333);
    assert(o_d[1][D_W-1:0]       == 32'h22222222);//Now we should see the second VC1 data
    assert(from_tx.vc_credit_gnt == 2'b10);//VC1 should already be granting another credit combinationally since we left it unbackpressured
    i_b                          <= '0;//And pop them both at once!
    from_tx.vc_target            <= '0;
    from_tx.packet.payload.data  <= '0;
    #(CLOCK_PERIOD / 4);//Credits granted combinationally
    //Same as before
    assert(o_v                   == 2'b11);
    assert(o_d[0][D_W-1:0]       == 32'h33333333);
    assert(o_d[1][D_W-1:0]       == 32'h22222222);//Now we should see the second VC1 data
    assert(from_tx.vc_credit_gnt == 2'b11);//Now since neither are backpressured, we're getting both!
    i_b <= 2'b00;//Pop VC1 AND VC1
    `WAITN(1);
    assert(o_v == 2'b00);//And all's back to normal!
    assert(from_tx.vc_credit_gnt == '0);

    //Push DEPTH - 1 packets to VC0 and VC1, and pop them all
    i_b                 <= 2'b11;
    from_tx.vc_target   <= 2'b01;//Start with VC0
    for (int ii = 0; ii < DEPTH - 1; ++ii) begin
        from_tx.packet.payload.data     <= (D_W)'(ii * 123);
        from_tx.packet.payload.last     <=   (1)'(ii * 123);
        from_tx.packet.routeinfo.addr   <= (A_W)'(ii * 123);
        `WAITN(1);
    end
    from_tx.vc_target   <= 2'b10;//Next do VC1
    for (int ii = 0; ii < DEPTH - 1; ++ii) begin
        from_tx.packet.payload.data     <= (D_W)'(ii * 456);
        from_tx.packet.payload.last     <=   (1)'(ii * 456);
        from_tx.packet.routeinfo.addr   <= (A_W)'(ii * 456);
        `WAITN(1);
    end
    i_b                         <= 2'b00;//Check them both!
    from_tx.vc_target           <= 2'b00;
    from_tx.packet.payload.data <= '0;
    for (int ii = 0; ii < DEPTH - 1; ++ii) begin
        assert(o_v == 2'b11);
        assert(o_d[0][D_W-1:0]          == (D_W)'(ii * 123));
        assert(o_d[0][D_W+A_W-1:D_W]    == (A_W)'(ii * 123));
        assert(o_d[0][D_W+A_W]          ==   (1)'(ii * 123));
        assert(o_d[1][D_W-1:0]          == (D_W)'(ii * 456));
        assert(o_d[1][D_W+A_W-1:D_W]    == (A_W)'(ii * 456));
        assert(o_d[1][D_W+A_W]          ==   (1)'(ii * 456));
        #(CLOCK_PERIOD / 4);//Credits granted combinationally
        assert(from_tx.vc_credit_gnt == 2'b11);
        `WAITN(1);
    end
    assert(o_v == 2'b00);
    assert(from_tx.vc_credit_gnt == '0);

    `WAITN(5);
    $finish;

    //verilator lint_restore
end

endmodule : credit_bp_rx_tb
