// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 * This register file is based on flip flops. Use this register file when
 * targeting FPGA synthesis or Verilator simulation.
 */
module ibex_register_file_ff #(
  parameter bit                   RV32E             = 0,
  parameter int unsigned          DataWidth         = 32,
  parameter bit                   DummyInstructions = 0,
  parameter bit                   WrenCheck         = 0,
  parameter bit                   RdataMuxCheck     = 0,
  parameter logic [DataWidth-1:0] WordZeroVal       = '0
) (
  // Clock and Reset
  input  logic                 clk_i,
  input  logic                 rst_ni,

  input  logic                 test_en_i,
  input  logic                 dummy_instr_id_i,
  input  logic                 dummy_instr_wb_i,

  //Read port R1
  input  logic [4:0]           raddr_a_i,
  output logic [DataWidth-1:0] rdata_a_o,

  output logic [DataWidth-1:0] rdata_msg1_o,
  output logic [DataWidth-1:0] rdata_msg2_o,
  output logic [DataWidth-1:0] rdata_msg3_o,

  //Read port R2
  input  logic [4:0]           raddr_b_i,
  output logic [DataWidth-1:0] rdata_b_o,


  // Write port W1
  input  logic [4:0]           waddr_a_i,
  input  logic [DataWidth-1:0] wdata_a_i,
  input  logic                 we_a_i,

  // This indicates whether spurious WE or non-one-hot encoded raddr are detected.
  output logic                 err_o,

  input logic input_valid,
  /* verilator lint_off UNUSEDSIGNAL */
  input logic [1:0] len_i,
  input logic [31:0] input_msg1,
  input logic [31:0] input_msg2,
  input logic [31:0] input_msg3,
  /* verilator lint_on UNUSEDSIGNAL */
  input logic [31:0] input_data,
  input logic [4:0] input_addr
);

  localparam int unsigned ADDR_WIDTH = RV32E ? 4 : 5;
  localparam int unsigned NUM_WORDS  = 2**ADDR_WIDTH;

  logic [DataWidth-1:0] rf_reg   [NUM_WORDS];
  //logic [DataWidth-1:0] rf_reg_msg [NUM_WORDS];
  logic [NUM_WORDS-1:0] we_a_dec;
  logic [NUM_WORDS-1:0] in_valid_dec;

  logic oh_raddr_a_err, oh_raddr_b_err, oh_we_err;

  always_comb begin : we_a_decoder
    for (int unsigned i = 0; i < NUM_WORDS; i++) begin
      we_a_dec[i] = (waddr_a_i == 5'(i)) ? we_a_i : 1'b0;
    end
  end

  always_comb begin : in_valid_decoder
    for (int unsigned i = 0; i < NUM_WORDS; i++) begin
      in_valid_dec[i] = (input_addr == 5'(i)) ? input_valid : 1'b0;
    end
  end


/* verilator lint_off UNUSEDSIGNAL */
  logic useless;
  assign useless = in_valid_dec[0];
  /* verilator lint_on UNUSEDSIGNAL */

  // SEC_CM: DATA_REG_SW.GLITCH_DETECT
  // This checks for spurious WE strobes on the regfile.
  if (WrenCheck) begin : gen_wren_check
    // Buffer the decoded write enable bits so that the checker
    // is not optimized into the address decoding logic.
    logic [NUM_WORDS-1:0] we_a_dec_buf;
    prim_buf #(
      .Width(NUM_WORDS)
    ) u_prim_buf (
      .in_i(we_a_dec),
      .out_o(we_a_dec_buf)
    );

    prim_onehot_check #(
      .AddrWidth(ADDR_WIDTH),
      .AddrCheck(1),
      .EnableCheck(1)
    ) u_prim_onehot_check (
      .clk_i,
      .rst_ni,
      .oh_i(we_a_dec_buf),
      .addr_i(waddr_a_i),
      .en_i(we_a_i),
      .err_o(oh_we_err)
    );
  end else begin : gen_no_wren_check
    logic unused_strobe;
    assign unused_strobe = we_a_dec[0]; // this is never read from in this case
    assign oh_we_err = 1'b0;
  end

  // No flops for R0 as it's hard-wired to 0
  for (genvar i = 1; i < NUM_WORDS; i++) begin : g_rf_flops
    logic [DataWidth-1:0] rf_reg_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_reg_q <= WordZeroVal;
      end else if (we_a_dec[i]) begin
        rf_reg_q <= wdata_a_i;
  //    end else if (in_valid_dec[i]) begin
    //    rf_reg_q <= input_data;
      end else begin

       /* unique case (len_i) // no need for 00?
        2'b01: begin
          if (in_valid_dec[i-1]) begin
            rf_reg_q <= input_msg1;
          end
        end
        2'b10: begin
          if (in_valid_dec[i-2]) begin
            rf_reg_q <= input_msg2;
          end
        end
        2'b11: begin
          if (in_valid_dec[i-3]) begin
            rf_reg_q <= input_msg3;
          end
        end
        default: begin
        end
        endcase */

      end
    end

    assign rf_reg[i] = rf_reg_q;
  end

  for (genvar i = 0; i < NUM_WORDS; i++) begin : g_rf_msg_flops
  /* verilator lint_off UNUSEDSIGNAL */
  logic [DataWidth-1:0] rf_reg_msg_q;
  /* verilator lint_on UNUSEDSIGNAL */


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rf_reg_msg_q <= WordZeroVal;
    end else begin
      if (in_valid_dec[i]) begin
        rf_reg_msg_q <= input_data;
        $display("rf_msg_reg_q[%0d] is written with value %0h, at %t", i, input_data, $time);

      end

    end
  end

  end


  // With dummy instructions enabled, R0 behaves as a real register but will always return 0 for
  // real instructions.
  if (DummyInstructions) begin : g_dummy_r0
    // SEC_CM: CTRL_FLOW.UNPREDICTABLE
    logic                 we_r0_dummy;
    logic [DataWidth-1:0] rf_r0_q;

    // Write enable for dummy R0 register (waddr_a_i will always be 0 for dummy instructions)
    assign we_r0_dummy = we_a_i & dummy_instr_wb_i;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_r0_q <= WordZeroVal;
      end else if (we_r0_dummy) begin
        rf_r0_q <= wdata_a_i;
      end
    end

    // Output the dummy data for dummy instructions, otherwise R0 reads as zero
    assign rf_reg[0] = dummy_instr_id_i ? rf_r0_q : WordZeroVal;

  end else begin : g_normal_r0
    logic unused_dummy_instr;
    assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;

    // R0 is nil
    assign rf_reg[0] = WordZeroVal;
  end

  if (RdataMuxCheck) begin : gen_rdata_mux_check
    // Encode raddr_a/b into one-hot encoded signals.
    logic [NUM_WORDS-1:0] raddr_onehot_a, raddr_onehot_b;
    logic [NUM_WORDS-1:0] raddr_onehot_a_buf, raddr_onehot_b_buf;
    logic [NUM_WORDS-1:0] raddr_msg1_onehot, raddr_msg2_onehot, raddr_msg3_onehot;

    assign raddr_msg1_onehot = {raddr_onehot_a[NUM_WORDS-2:1], raddr_onehot_a[NUM_WORDS-1]};
    assign raddr_msg2_onehot = {raddr_msg1_onehot[NUM_WORDS-2:1], raddr_msg1_onehot[NUM_WORDS-1]};
    assign raddr_msg3_onehot = {raddr_msg2_onehot[NUM_WORDS-2:1], raddr_msg2_onehot[NUM_WORDS-1]};
    
    prim_onehot_enc #(
      .OneHotWidth(NUM_WORDS)
    ) u_prim_onehot_enc_raddr_a (
      .in_i  (raddr_a_i),
      .en_i  (1'b1),
      .out_o (raddr_onehot_a)
    );

    prim_onehot_enc #(
      .OneHotWidth(NUM_WORDS)
    ) u_prim_onehot_enc_raddr_b (
      .in_i  (raddr_b_i),
      .en_i  (1'b1),
      .out_o (raddr_onehot_b)
    );

    // Buffer the one-hot encoded signals so that the checkers
    // are not optimized.
    prim_buf #(
      .Width(NUM_WORDS)
    ) u_prim_buf_raddr_a (
      .in_i (raddr_onehot_a),
      .out_o(raddr_onehot_a_buf)
    );

    prim_buf #(
      .Width(NUM_WORDS)
    ) u_prim_buf_raddr_b (
      .in_i (raddr_onehot_b),
      .out_o(raddr_onehot_b_buf)
    );

    // SEC_CM: DATA_REG_SW.GLITCH_DETECT
    // Check the one-hot encoded signals for glitches.
    prim_onehot_check #(
      .AddrWidth(ADDR_WIDTH),
      .OneHotWidth(NUM_WORDS),
      .AddrCheck(1),
      // When AddrCheck=1 also EnableCheck needs to be 1.
      .EnableCheck(1)
    ) u_prim_onehot_check_raddr_a (
      .clk_i,
      .rst_ni,
      .oh_i   (raddr_onehot_a_buf),
      .addr_i (raddr_a_i),
      // Set enable=1 as address is always valid.
      .en_i   (1'b1),
      .err_o  (oh_raddr_a_err)
    );

    prim_onehot_check #(
      .AddrWidth(ADDR_WIDTH),
      .OneHotWidth(NUM_WORDS),
      .AddrCheck(1),
      // When AddrCheck=1 also EnableCheck needs to be 1.
      .EnableCheck(1)
    ) u_prim_onehot_check_raddr_b (
      .clk_i,
      .rst_ni,
      .oh_i   (raddr_onehot_b_buf),
      .addr_i (raddr_b_i),
      // Set enable=1 as address is always valid.
      .en_i   (1'b1),
      .err_o  (oh_raddr_b_err)
    );

    // MUX register to rdata_a/b_o according to raddr_a/b_onehot.
    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_rdata_a_mux (
      .clk_i,
      .rst_ni,
      .in_i  (rf_reg),
      .sel_i (raddr_onehot_a),
      .out_o (rdata_a_o)
    );

    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_msg1_a_mux (
      .clk_i,
      .rst_ni,
      .in_i  (rf_reg),
      .sel_i (raddr_msg1_onehot),
      .out_o (rdata_msg1_o)
    );

    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_msg2_a_mux (
      .clk_i,
      .rst_ni,
      .in_i  (rf_reg),
      .sel_i (raddr_msg2_onehot),
      .out_o (rdata_msg2_o)
    );

    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_msg3_a_mux (
      .clk_i,
      .rst_ni,
      .in_i  (rf_reg),
      .sel_i (raddr_msg3_onehot),
      .out_o (rdata_msg3_o)
    );

    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_rdata_b_mux (
      .clk_i,
      .rst_ni,
      .in_i  (rf_reg),
      .sel_i (raddr_onehot_b),
      .out_o (rdata_b_o)
    );
  end else begin : gen_no_rdata_mux_check
    assign rdata_a_o = rf_reg[raddr_a_i];
    assign rdata_b_o = rf_reg[raddr_b_i];
    assign rdata_msg1_o = rf_reg[raddr_a_i+1];
    assign rdata_msg2_o = rf_reg[raddr_a_i+2];
    assign rdata_msg3_o = rf_reg[raddr_a_i+3];
    assign oh_raddr_a_err = 1'b0;
    assign oh_raddr_b_err = 1'b0;
  end

  assign err_o = oh_raddr_a_err || oh_raddr_b_err || oh_we_err;

  // Signal not used in FF register file
  logic unused_test_en;
  assign unused_test_en = test_en_i;

endmodule
