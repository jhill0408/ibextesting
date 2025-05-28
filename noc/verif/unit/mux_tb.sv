/**
 * File    mux_tb.sv
 * Brief   mux testbench
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

module mux_tb;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam NUM_DUTS = 4;

localparam int N [NUM_DUTS-1:0] = '{ 6,  4,  3,  2};
localparam int W [NUM_DUTS-1:0] = '{32, 32, 32, 32};

generate
for (genvar ii = 0; ii < NUM_DUTS; ++ii) begin : gen_dut
    localparam int L = $clog2(N[ii]);

    /* ------------------------------------------------------------------------------------------------
     * DUT Connections
     * --------------------------------------------------------------------------------------------- */

    logic                [L-1:0] s;
    logic [N[ii]-1:0][W[ii]-1:0] i;
    logic            [W[ii]-1:0] o;

    /* ------------------------------------------------------------------------------------------------
     * DUT
     * --------------------------------------------------------------------------------------------- */

    mux #(
        .N(N[ii]),
        .W(W[ii])
    ) dut (
        .s(s),
        .i(i),
        .o(o)
    );

    /* ------------------------------------------------------------------------------------------------
     * Monitoring
     * --------------------------------------------------------------------------------------------- */

    initial begin
        $monitor(
           "DUT %d : t=%t s=%h i=%h o=%h",
            ii,    $time, s,   i,   o
        );
    end

end : gen_dut
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //DUT 0 tests

    gen_dut[0].s    <= 1'b0;
    gen_dut[0].i[0] <= 32'hABCDABCD;
    gen_dut[0].i[1] <= 32'h12341234;
    #1;
    assert(gen_dut[0].o == 32'hABCDABCD);
    gen_dut[0].s    <= 1'b1;
    #1;
    assert(gen_dut[0].o == 32'h12341234);

    //DUT 1 tests

    gen_dut[1].s    <= 2'b00;
    gen_dut[1].i[0] <= 32'hABCDABCD;
    gen_dut[1].i[1] <= 32'h12341234;
    gen_dut[1].i[2] <= 32'h56785678;
    #1;
    assert(gen_dut[1].o == 32'hABCDABCD);
    gen_dut[1].s    <= 2'b01;
    #1;
    assert(gen_dut[1].o == 32'h12341234);
    gen_dut[1].s    <= 2'b10;
    #1;
    assert(gen_dut[1].o == 32'h56785678);

    //DUT 2 tests

    gen_dut[2].s    <= 2'b00;
    gen_dut[2].i[0] <= 32'hABCDABCD;
    gen_dut[2].i[1] <= 32'h12341234;
    gen_dut[2].i[2] <= 32'h56785678;
    gen_dut[2].i[3] <= 32'hEFEFEFEF;
    #1;
    assert(gen_dut[2].o == 32'hABCDABCD);
    gen_dut[2].s    <= 2'b01;
    #1;
    assert(gen_dut[2].o == 32'h12341234);
    gen_dut[2].s    <= 2'b10;
    #1;
    assert(gen_dut[2].o == 32'h56785678);
    gen_dut[2].s    <= 2'b11;
    #1;
    assert(gen_dut[2].o == 32'hEFEFEFEF);

    //DUT 3 tests

    gen_dut[3].s    <= 3'b000;
    gen_dut[3].i[0] <= 32'hABCDABCD;
    gen_dut[3].i[1] <= 32'h12341234;
    gen_dut[3].i[2] <= 32'h56785678;
    gen_dut[3].i[3] <= 32'hEFEFEFEF;
    gen_dut[3].i[4] <= 32'h00000000;
    gen_dut[3].i[5] <= 32'hFFFFFFFF;
    #1;
    assert(gen_dut[3].o == 32'hABCDABCD);
    gen_dut[3].s    <= 3'b001;
    #1;
    assert(gen_dut[3].o == 32'h12341234);
    gen_dut[3].s    <= 3'b010;
    #1;
    assert(gen_dut[3].o == 32'h56785678);
    gen_dut[3].s    <= 3'b011;
    #1;
    assert(gen_dut[3].o == 32'hEFEFEFEF);
    gen_dut[3].s    <= 3'b100;
    #1;
    assert(gen_dut[3].o == 32'h00000000);
    gen_dut[3].s    <= 3'b101;
    #1;
    assert(gen_dut[3].o == 32'hFFFFFFFF);

    #10;
    $finish;

    //verilator lint_restore
end

endmodule : mux_tb
