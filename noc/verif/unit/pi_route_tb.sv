/**
 * File    pi_route_tb.sv
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

module pi_route_tb;

import common_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam N     = DEFAULT_N;   // number of clients
localparam A_W   = DEFAULT_A_W; // log number of clients ($clog2(N) + 1)
localparam posl  = 1;           // which level
localparam posx  = 4'b1010;     // which position
localparam VC_W  = DEFAULT_VC_W;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;   // clock
logic rst;   // reset

//Datapath and control signals
//Lower VCs are statically prioritized over higher VCs
//So with VC_W == 2 for example, VC0 should be used as a "reply" VC and VC1 for "requests"
logic [VC_W-1:0]             l_i_v;     // left input valid
logic [VC_W-1:0]             r_i_v;     // right input valid
logic [VC_W-1:0]             u0_i_v;    // up0 input valid
logic [VC_W-1:0]             u1_i_v;    // up1 input valid
logic [VC_W-1:0]             l_i_bp;    // left input is backpressured
logic [VC_W-1:0]             r_i_bp;    // right input is backpressured
logic [VC_W-1:0]             u0_i_bp;   // up0 input is backpressured
logic [VC_W-1:0]             u1_i_bp;   // up1 input is backpressured
logic [VC_W-1:0][A_W-1:0]    l_i_addr;  // left input addr
logic [VC_W-1:0][A_W-1:0]    r_i_addr;  // right input addr
logic [VC_W-1:0][A_W-1:0]    u0_i_addr; // up0 input addr
logic [VC_W-1:0][A_W-1:0]    u1_i_addr; // up1 input addr
logic [VC_W-1:0]             l_o_v;     // valid for l mux
logic [VC_W-1:0]             r_o_v;     // valid for r mux
logic [VC_W-1:0]             u0_o_v;    // valid for u0 mux
logic [VC_W-1:0]             u1_o_v;    // valid for u1 mux
logic [VC_W-1:0]             l_o_bp;    // left output is backpressured
logic [VC_W-1:0]             r_o_bp;    // right output is backpressured
logic [VC_W-1:0]             u0_o_bp;   // up0 output is backpressured
logic [VC_W-1:0]             u1_o_bp;   // up1 output is backpressured
logic [$clog2(VC_W*3)-1:0]   l_sel;     // select for l mux
logic [$clog2(VC_W*3)-1:0]   r_sel;     // select for r mux
logic [$clog2(VC_W*2)-1:0]   u0_sel;    // select for u0 mux
logic [$clog2(VC_W*2)-1:0]   u1_sel;    // select for u1 mux

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

pi_route #(
    .N(N),
    .A_W(A_W),
    .posl(posl),
    .posx(posx),
    .VC_W(VC_W)
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
        "t=%t rst=%b l_i_v=%b r_i_v=%b u0_i_v=%b u1_i_v=%b, l_i_bp=%b r_i_bp=%b u0_i_bp=%b u1_i_bp=%b l_i_addr=%h r_i_addr=%h u0_i_addr=%h u0_i_addr=%h l_o_bp=%b r_o_bp=%b u0_o_bp=%b u1_o_bp=%b",
        $time, rst,  l_i_v,   r_i_v,   u0_i_v,   u1_i_v,    l_i_bp,   r_i_bp,   u0_i_bp,   u1_i_bp,   l_i_addr,   r_i_addr,   u0_i_addr,   u0_i_addr,   l_o_bp,   r_o_bp,   u0_o_bp,   u1_o_bp
    );
end

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Assert reset for a couple clock cycles, and set initial inputs
    rst         <= 1'b1;
    l_i_v       <= '0;
    r_i_v       <= '0;
    u0_i_v      <= '0;
    u1_i_v      <= '0;
    l_i_addr    <= '0;
    r_i_addr    <= '0;
    u0_i_addr   <= '0;
    u1_i_addr   <= '0;
    l_o_bp      <= '0;
    r_o_bp      <= '0;
    u0_o_bp     <= '0;
    u1_o_bp     <= '0;
    `WAITN(2);
    rst <= 1'b0;

    //Simple one-packet-at-a-time tests

    //Routing a packet from the left VC0 to the right VC0 (turning)
    l_i_v       <= 2'b01;
    l_i_addr[0] <= 4'b1010;//Top A_W - posl - 1 = 2 bits are the same as posx, and the posl'th bit is set, so this should go to the right
    #(CLOCK_PERIOD / 4);//This will occur combinationaly
    assert(l_i_bp   == '0);//There shouldn't be backpressure since this is the only packet at the moment
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == 2'b01);//The packet should be routed to the right VC0
    assert(u0_o_v   == '0);
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b100);//4 means we should mux from left's VC0
    assert(u0_sel   == 2'b00);
    assert(u1_sel   == 2'b00);
    `WAITN(1);
    r_o_bp      <= 2'b01;//Backpressure for a cycle
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b01);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    assert(u1_o_v   == '0);
    `WAITN(1);
    l_i_v       <= '0;
    l_i_addr[0] <= '0;
    r_o_bp      <= '0;

    //Routing a packet from the right VC1 to the up1 VC1 (ascending)
    r_i_v       <= 2'b10;
    r_i_addr[1] <= 4'b1100;//Top A_W - posl - 1 = 2 bits are different from posx, so this should go up
    #(CLOCK_PERIOD / 4);//This will occur combinationaly
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);//There shouldn't be backpressure since this is the only packet at the moment
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);//R packets never go to u0
    assert(u1_o_v   == 2'b10);//The packet should be routed to the up0 VC1
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b000);
    assert(u0_sel   == 2'b00);
    assert(u1_sel   == 2'b01);//1 means we should mux from right's VC1
    `WAITN(1);
    u1_o_bp     <= 2'b10;
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == '0);
    assert(r_i_bp   == 2'b10);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    assert(u1_o_v   == '0);
    `WAITN(1);
    r_i_v       <= '0;
    r_i_addr[1] <= '0;
    u1_o_bp     <= '0;

    //Routing a packet from the left VC1 to the up0 VC1 (ascending)
    l_i_v       <= 2'b10;
    l_i_addr[1] <= 4'b1100;//Top A_W - posl - 1 = 2 bits are different from posx, so this should go up
    #(CLOCK_PERIOD / 4);//This will occur combinationaly
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);//There shouldn't be backpressure since this is the only packet at the moment
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b10);//The packet should be routed to the up0 VC1
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b000);
    assert(u0_sel   == 2'b11);//3 means we should mux from left's VC1
    assert(u1_sel   == 2'b00);
    `WAITN(1);
    u0_o_bp     <= 2'b10;
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b10);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    assert(u1_o_v   == '0);
    `WAITN(1);
    l_i_v       <= '0;
    l_i_addr[1] <= '0;
    u0_o_bp     <= '0;

    //Routing a packet from the u0 VC0 to the left VC0 (descending)
    u0_i_v       <= 2'b01;
    u0_i_addr[0] <= 4'b1101;//Bit posl=1 is clear, so this should go to the left
    #(CLOCK_PERIOD / 4);//This will occur combinationaly
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);//There shouldn't be backpressure since this is the only packet at the moment
    assert(u1_i_bp  == '0);
    assert(l_o_v    == 2'b01);//The packet should be routed to the left VC0
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b010);//2 means we should mux from up0's VC0
    assert(r_sel    == 3'b000);
    assert(u0_sel   == 2'b00);
    assert(u1_sel   == 2'b00);
    l_o_bp       <= 2'b10;//Wrong VC backpressured, this should have no effect
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == 2'b01);
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b010);
    assert(r_sel    == 3'b000);
    assert(u0_sel   == 2'b00);
    assert(u1_sel   == 2'b00);
    `WAITN(1);
    u0_i_v       <= '0;
    u0_i_addr[0] <= '0;
    l_o_bp       <= '0;

    //Routing a packet from the u1 VC1 to the right VC1 (descending)
    u1_i_v       <= 2'b10;
    u1_i_addr[1] <= 4'b0010;//Bit posl=1 is set, so this should go to the right
    #(CLOCK_PERIOD / 4);//This will occur combinationaly
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);//There shouldn't be backpressure since this is the only packet at the moment
    assert(l_o_v    == '0);
    assert(r_o_v    == 2'b10);//The packet should be routed to the right VC1
    assert(u0_o_v   == '0);
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b001);//1 means we should mux from up0's VC1
    assert(u0_sel   == 2'b00);
    assert(u1_sel   == 2'b00);
    r_o_bp       <= 2'b01;//Wrong VC backpressured, this should have no effect
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == 2'b10);
    assert(u0_o_v   == '0);
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b001);
    assert(u0_sel   == 2'b00);
    assert(u1_sel   == 2'b00);
    `WAITN(1);
    u1_i_v       <= '0;
    u1_i_addr[1] <= '0;
    r_o_bp       <= '0;

    //Multiple-packets-at-a-time tests

    //LVC0 -> RVC0, RVC1 -> U1VC1, U0VC0 -> LVC0, all at once
    l_i_v        <= 2'b01;
    l_i_addr[0]  <= 4'b1010;
    r_i_v        <= 2'b10;
    r_i_addr[1]  <= 4'b1100;
    u0_i_v       <= 2'b01;
    u0_i_addr[0] <= 4'b1101;
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == 2'b01);
    assert(r_o_v    == 2'b01);
    assert(u0_o_v   == 2'b00);
    assert(u1_o_v   == 2'b10);
    assert(l_sel    == 3'b010);
    assert(r_sel    == 3'b100);
    assert(u0_sel   == 2'b00);
    assert(u1_sel   == 2'b01);//
    `WAITN(1);
    //Backpressure everything
    l_o_bp       <= '1;
    r_o_bp       <= '1;
    u0_o_bp      <= '1;
    u1_o_bp      <= '1;
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b01);
    assert(r_i_bp   == 2'b10);
    assert(u0_i_bp  == 2'b01);
    assert(u1_i_bp  == 2'b00);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == '0);
    assert(u1_o_v   == '0);
    `WAITN(1);
    l_i_v        <= '0;
    l_i_addr[0]  <= '0;
    l_o_bp       <= '0;
    r_i_v        <= '0;
    r_i_addr[0]  <= '0;
    r_o_bp       <= '0;
    u0_i_v       <= '0;
    u0_i_addr[0] <= '0;
    u0_o_bp      <= '0;
    u1_o_bp      <= '0;

    //Conflict within a direction (both want to ascend)
    l_i_v        <= 2'b11;
    l_i_addr[0]  <= 4'b0100;
    l_i_addr[1]  <= 4'b0100;
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b10);//VC1 should be backpressured
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b01);//VC0 is statically prioritized over VC1
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b000);
    assert(u0_sel   == 2'b10);
    assert(u1_sel   == 2'b00);
    `WAITN(1);
    //There should be NO round-robin between VCs in a single direction
    assert(l_i_bp   == 2'b10);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b01);
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b000);
    assert(u0_sel   == 2'b10);
    assert(u1_sel   == 2'b00);
    `WAITN(1);
    u0_o_bp      <= 2'b10;//Backpressure VC1, nothing should change
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b10);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b01);
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b000);
    assert(u0_sel   == 2'b10);
    assert(u1_sel   == 2'b00);
    `WAITN(1);
    u0_o_bp      <= 2'b01;//Backpressure VC0, VC1 should get a turn
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b01);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b10);//Now VC1 gets a turn!
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b000);
    assert(u0_sel   == 2'b11);
    assert(u1_sel   == 2'b00);
    `WAITN(1);
    u0_o_bp      <= 2'b00;//No more backpressure, back to normal
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == 2'b10);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b01);
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b000);
    assert(u0_sel   == 2'b10);
    assert(u1_sel   == 2'b00);
    `WAITN(1);
    l_i_v        <= 2'b10;//Now just VC1 is left!
    #(CLOCK_PERIOD / 4);
    assert(l_i_bp   == '0);
    assert(r_i_bp   == '0);
    assert(u0_i_bp  == '0);
    assert(u1_i_bp  == '0);
    assert(l_o_v    == '0);
    assert(r_o_v    == '0);
    assert(u0_o_v   == 2'b10);//VC1 gets a turn!
    assert(u1_o_v   == '0);
    assert(l_sel    == 3'b000);
    assert(r_sel    == 3'b000);
    assert(u0_sel   == 2'b11);
    assert(u1_sel   == 2'b00);
    `WAITN(1);
    l_i_v        <= '0;
    l_i_addr[0]  <= '0;
    l_i_addr[1]  <= '0;

    //Conflict between directions (both to RVC1)
    l_i_v        <= 2'b10;
    l_i_addr[1]  <= 4'b1010;//Turning to the right
    u1_i_v       <= 2'b10;
    u1_i_addr[1] <= 4'b0010;//Descending to the right
    #(CLOCK_PERIOD / 4);
    for (int ii = 0; ii < 10; ++ii) begin
        assert(l_i_bp   == '0);
        assert(r_i_bp   == '0);
        assert(u0_i_bp  == '0);
        assert(u1_i_bp  == 2'b10);//It's L's turn
        assert(l_o_v    == '0);
        assert(r_o_v    == 2'b10);
        assert(u0_o_v   == '0);
        assert(u1_o_v   == '0);
        assert(l_sel    == 3'b000);
        assert(r_sel    == 3'b101);//Route from L's VC1
        assert(u0_sel   == 2'b00);
        assert(u1_sel   == 2'b00);
        `WAITN(1);
        assert(l_i_bp   == 2'b10);//It's U1's turn
        assert(r_i_bp   == '0);
        assert(u0_i_bp  == '0);
        assert(u1_i_bp  == '0);
        assert(l_o_v    == '0);
        assert(r_o_v    == 2'b10);
        assert(u0_o_v   == '0);
        assert(u1_o_v   == '0);
        assert(l_sel    == 3'b000);
        assert(r_sel    == 3'b001);//Route from U1's VC1
        assert(u0_sel   == 2'b00);
        assert(u1_sel   == 2'b00);
        `WAITN(1);
    end
    `WAITN(1);
    r_o_bp      <= 2'b10;//Backpressure VC1, everything should stop
    #(CLOCK_PERIOD / 4);
    for (int ii = 0; ii < 3; ++ii) begin
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == '0);
        assert(u0_i_bp  == '0);
        assert(u1_i_bp  == 2'b10);
        assert(l_o_v    == '0);
        assert(r_o_v    == '0);
        assert(u0_o_v   == '0);
        assert(l_sel    == 3'b000);
        assert(r_sel    == 3'b000);
        assert(u0_sel   == 2'b00);
        assert(u1_sel   == 2'b00);
        `WAITN(1);
    end
    r_o_bp       <= '0;
    l_i_v        <= '0;
    l_i_addr[1]  <= '0;
    u1_i_v       <= '0;
    u1_i_addr[1] <= '0;
    `WAITN(1);//So we end up in the L turn state

    //More tricky tests

    //Conflicts between different directions on different VCs (also all VCs at once)
    l_i_v        <= 2'b11;
    l_i_addr[0]  <= 4'b0101;//Ascending (to u0)
    l_i_addr[1]  <= 4'b0111;//Ascending (to u0)
    r_i_v        <= 2'b11;
    r_i_addr[0]  <= 4'b1000;//Going left!
    r_i_addr[1]  <= 4'b0110;//Ascending (to u1)
    u0_i_v       <= 2'b11;
    u0_i_addr[0] <= 4'b1011;//Descending to the right
    u0_i_addr[1] <= 4'b1001;//Descending to the left
    u1_i_v       <= 2'b11;
    u1_i_addr[0] <= 4'b1001;//Descending to the left
    u1_i_addr[1] <= 4'b1011;//Descending to the right
    #(CLOCK_PERIOD / 4);
    for (int ii = 0; ii < 10; ++ii) begin
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == 2'b01);
        assert(u0_i_bp  == 2'b11);
        assert(u1_i_bp  == 2'b11);
        assert(l_o_v    == 2'b00);
        assert(r_o_v    == 2'b00);
        assert(u0_o_v   == 2'b01);
        assert(u1_o_v   == 2'b10);
        assert(l_sel    == 3'b000);
        assert(r_sel    == 3'b000);
        assert(u0_sel   == 2'b10);
        assert(u1_sel   == 2'b01);
        `WAITN(1);
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == 2'b00);
        assert(u0_i_bp  == 2'b11);
        assert(u1_i_bp  == 2'b11);
        assert(l_o_v    == 2'b01);
        assert(r_o_v    == 2'b00);
        assert(u0_o_v   == 2'b01);
        assert(u1_o_v   == 2'b10);
        assert(l_sel    == 3'b100);
        assert(r_sel    == 3'b000);
        assert(u0_sel   == 2'b10);
        assert(u1_sel   == 2'b01);
        `WAITN(1);
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == 2'b01);
        assert(u0_i_bp  == 2'b00);
        assert(u1_i_bp  == 2'b11);
        assert(l_o_v    == 2'b10);
        assert(r_o_v    == 2'b01);
        assert(u0_o_v   == 2'b01);
        assert(u1_o_v   == 2'b10);
        assert(l_sel    == 3'b011);
        assert(r_sel    == 3'b010);
        assert(u0_sel   == 2'b10);
        assert(u1_sel   == 2'b01);
        `WAITN(1);
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == 2'b01);
        assert(u0_i_bp  == 2'b11);
        assert(u1_i_bp  == 2'b00);
        assert(l_o_v    == 2'b01);
        assert(r_o_v    == 2'b10);
        assert(u0_o_v   == 2'b01);
        assert(u1_o_v   == 2'b10);
        assert(l_sel    == 3'b000);
        assert(r_sel    == 3'b001);
        assert(u0_sel   == 2'b10);
        assert(u1_sel   == 2'b01);
        `WAITN(1);
    end
    l_o_bp <= 2'b01;//Backpressure l VC0
    #(CLOCK_PERIOD / 4);
    for (int ii = 0; ii < 10; ++ii) begin
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == 2'b01);
        assert(u0_i_bp  == 2'b11);
        assert(u1_i_bp  == 2'b11);
        assert(l_o_v    == 2'b00);
        assert(r_o_v    == 2'b00);
        assert(u0_o_v   == 2'b01);
        assert(u1_o_v   == 2'b10);
        assert(l_sel    == 3'b000);
        assert(r_sel    == 3'b000);
        assert(u0_sel   == 2'b10);
        assert(u1_sel   == 2'b01);
        `WAITN(1);
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == 2'b01);
        assert(u0_i_bp  == 2'b11);
        assert(u1_i_bp  == 2'b11);
        assert(l_o_v    == 2'b00);
        assert(r_o_v    == 2'b00);
        assert(u0_o_v   == 2'b01);
        assert(u1_o_v   == 2'b10);
        assert(l_sel    == 3'b000);
        assert(r_sel    == 3'b000);
        assert(u0_sel   == 2'b10);
        assert(u1_sel   == 2'b01);
        `WAITN(1);
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == 2'b01);
        assert(u0_i_bp  == 2'b00);
        assert(u1_i_bp  == 2'b11);
        assert(l_o_v    == 2'b10);
        assert(r_o_v    == 2'b01);
        assert(u0_o_v   == 2'b01);
        assert(u1_o_v   == 2'b10);
        assert(l_sel    == 3'b011);
        assert(r_sel    == 3'b010);
        assert(u0_sel   == 2'b10);
        assert(u1_sel   == 2'b01);
        `WAITN(1);
        assert(l_i_bp   == 2'b10);
        assert(r_i_bp   == 2'b01);
        assert(u0_i_bp  == 2'b11);
        assert(u1_i_bp  == 2'b01);
        assert(l_o_v    == 2'b00);
        assert(r_o_v    == 2'b10);
        assert(u0_o_v   == 2'b01);
        assert(u1_o_v   == 2'b10);
        assert(l_sel    == 3'b000);
        assert(r_sel    == 3'b001);
        assert(u0_sel   == 2'b10);
        assert(u1_sel   == 2'b01);
        `WAITN(1);
    end
    l_o_bp       <= '0;
    l_i_v        <= '0;
    l_i_addr[0]  <= '0;
    l_i_addr[1]  <= '0;
    r_i_v        <= '0;
    r_i_addr[0]  <= '0;
    r_i_addr[1]  <= '0;
    u0_i_v       <= '0;
    u0_i_addr[0] <= '0;
    u0_i_addr[1] <= '0;
    u1_i_v       <= '0;
    u1_i_addr[0] <= '0;
    u1_i_addr[1] <= '0;
    `WAITN(1);

    //TODO other hard tests (perhaps also with backpressure)

    `WAITN(5);
    $finish;

    //verilator lint_restore
end

endmodule : pi_route_tb
