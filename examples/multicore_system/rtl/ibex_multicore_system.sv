// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// VCS does not support overriding enum and string parameters via command line. Instead, a `define
// is used that can be set from the command line. If no value has been specified, this gives a
// default. Other simulators don't take the detour via `define and can override the corresponding
// parameters directly.
`ifndef RV32M
  `define RV32M ibex_pkg::RV32MFast
`endif

`ifndef RV32B
  `define RV32B ibex_pkg::RV32BNone
`endif

`ifndef RegFile
  `define RegFile ibex_pkg::RegFileFF
`endif

/**
 * Ibex simple system
 *
 * This is a basic system consisting of an ibex, a 1 MB sram for instruction/data
 * and a small memory mapped control module for outputting ASCII text and
 * controlling/halting the simulation from the software running on the ibex.
 *
 * It is designed to be used with verilator but should work with other
 * simulators, a small amount of work may be required to support the
 * simulator_ctrl module.
 */

module ibex_multicore_system (
  input IO_CLK,
  input IO_RST_N
);

  parameter bit                 SecureIbex               = 1'b0;
  parameter bit                 ICacheScramble           = 1'b0;
  parameter bit                 PMPEnable                = 1'b0;
  parameter int unsigned        PMPGranularity           = 0;
  parameter int unsigned        PMPNumRegions            = 4;
  parameter int unsigned        MHPMCounterNum           = 0;
  parameter int unsigned        MHPMCounterWidth         = 40;
  parameter bit                 RV32E                    = 1'b0;
  parameter ibex_pkg::rv32m_e   RV32M                    = `RV32M;
  parameter ibex_pkg::rv32b_e   RV32B                    = `RV32B;
  parameter ibex_pkg::regfile_e RegFile                  = `RegFile;
  parameter bit                 BranchTargetALU          = 1'b0;
  parameter bit                 WritebackStage           = 1'b0;
  parameter bit                 ICache                   = 1'b0;
  parameter bit                 DbgTriggerEn             = 1'b0;
  parameter bit                 ICacheECC                = 1'b0;
  parameter bit                 BranchPredictor          = 1'b0;
  parameter                     SRAMInitFile             = "";
  parameter int unsigned        CPUCount                 = 4;

  logic clk_sys = 1'b0, rst_sys_n;

  typedef enum logic {
    CoreD,
    CoreE
  } bus_host_e;

  typedef enum logic[1:0] {
    Ram,
    SimCtrl,
    Timer
  } bus_device_e;

  localparam int NrDevices = 3;
  localparam int NrHosts = CPUCount;

/*
  logic valid01;
  logic valid10;
  logic [31:0] data01;
  logic [31:0] data10;
  logic [4:0] addr01;
  logic [4:0] addr10;
  */
 /* verilator lint_off UNDRIVEN */
 /* verilator lint_off UNUSEDSIGNAL */
  logic [NrHosts-1:0] valid_i;
  
  logic [NrHosts-1:0] valid_o;
  logic [NrHosts-1:0] [31:0] data_i;
  logic [NrHosts-1:0] [31:0] data_o;
  logic [NrHosts-1:0] [4:0] addr_i;
  logic [NrHosts-1:0] [4:0] addr_o;
  logic [NrHosts-1:0] [1:0] len_i;
  logic [NrHosts-1:0] [1:0] len_o;
  logic [NrHosts-1:0] [31:0] msg1_data;
  logic [NrHosts-1:0] [31:0] msg2_data;
  logic [NrHosts-1:0] [31:0] msg3_data;
  logic [NrHosts-1:0] [31:0] msg1_data_i;
  logic [NrHosts-1:0] [31:0] msg2_data_i;
  logic [NrHosts-1:0] [31:0] msg3_data_i;

  /* verilator lint_on UNUSEDSIGNAL */
  /* verilator lint_on UNDRIVEN */

  // interrupts
  logic timer_irq;

  // host and device signals
  logic           host_req    [NrHosts];
  logic           host_gnt    [NrHosts];
  logic [31:0]    host_addr   [NrHosts];
  logic           host_we     [NrHosts];
  logic [ 3:0]    host_be     [NrHosts];
  logic [31:0]    host_wdata  [NrHosts];
  logic           host_rvalid [NrHosts];
  logic [31:0]    host_rdata  [NrHosts];
  logic           host_err    [NrHosts];

/*
  logic [6:0]     data_rdata_intg1;
  logic [6:0]     instr_rdata_intg1;
  logic [6:0]     data_rdata_intg2;
  logic [6:0]     instr_rdata_intg2;
  */

  logic [NrHosts - 1 :0] [6:0] data_rdata_intg;
  logic [NrHosts - 1 :0] [6:0] instr_rdata_intg;

  // devices (slaves)
  logic           device_req    [NrDevices];
  logic [31:0]    device_addr   [NrDevices];
  logic           device_we     [NrDevices];
  logic [ 3:0]    device_be     [NrDevices];
  logic [31:0]    device_wdata  [NrDevices];
  logic           device_rvalid [NrDevices];
  logic [31:0]    device_rdata  [NrDevices];
  logic           device_err    [NrDevices];

  // wires for instr bus
  logic           ram_instr_req [1];
  logic [31:0]    ram_instr_addr [1]  ;
  //logic           ram_instr_we  [1]   ;
 // logic [ 3:0]    ram_instr_be  [1]   ;
 // logic [31:0]    ram_instr_wdata [1] ;
  logic           ram_instr_rvalid [1];
  logic [31:0]    ram_instr_rdata [1] ;
  //logic           ram_instr_err  [1]  ;

  // Device address mapping
  logic [31:0] cfg_device_addr_base [NrDevices];
  logic [31:0] cfg_device_addr_mask [NrDevices];
  assign cfg_device_addr_base[Ram] = 32'h100000;
  assign cfg_device_addr_mask[Ram] = ~32'hFFFFF; // 1 MB
  //assign cfg_device_addr_base[Ram2] = 32'h300000;
  //assign cfg_device_addr_mask[Ram2] = ~32'hFFFFF; // 1 MB
  assign cfg_device_addr_base[SimCtrl] = 32'h20000;
  assign cfg_device_addr_mask[SimCtrl] = ~32'h3FF; // 1 kB
  assign cfg_device_addr_base[Timer] = 32'h30000;
  assign cfg_device_addr_mask[Timer] = ~32'h3FF; // 1 kB

  // Instruction fetch signals
  logic instr_req [NrHosts];
  logic instr_gnt [NrHosts];
  logic instr_rvalid [NrHosts];
  logic [31:0] instr_addr [NrHosts];
  logic [31:0] instr_rdata [NrHosts];
  /* verilator lint_off UNUSEDSIGNAL */
  logic instr_err [NrHosts];
  /* verilator lint_on UNUSEDSIGNAL */

  //assign instr_gnt = instr_req;
  //assign instr_err = 'b0;


  /*
  logic instr_req1;
  logic instr_gnt1;
  logic instr_rvalid1;
  logic [31:0] instr_addr1;
  logic [31:0] instr_rdata1;
  logic instr_err1;

  assign instr_gnt1 = instr_req1;
  assign instr_err1 = '0;

  logic instr_req2;
  logic instr_gnt2;
  logic instr_rvalid2;
  logic [31:0] instr_addr2;
  logic [31:0] instr_rdata2;
  logic instr_err2;

  assign instr_gnt2 = instr_req2;
  assign instr_err2 = '0;
  */

  `ifdef VERILATOR
    assign clk_sys = IO_CLK;
    assign rst_sys_n = IO_RST_N;
  `else
    initial begin
      rst_sys_n = 1'b0;
      #8
      rst_sys_n = 1'b1;
    end
    always begin
      #1 clk_sys = 1'b0;
      #1 clk_sys = 1'b1;
    end
  `endif

  // Tie-off unused error signals
  assign device_err[Ram] = 1'b0;
  //assign device_err[Ram2] = 1'b0;
  assign device_err[SimCtrl] = 1'b0;

  bus #(
    .NrDevices    ( NrDevices ),
    .NrHosts      ( NrHosts   ),
    .DataWidth    ( 32        ),
    .AddressWidth ( 32        )
  ) u_bus1 (
    .clk_i               (clk_sys),
    .rst_ni              (rst_sys_n),

    .host_req_i          (host_req     ),
    .host_gnt_o          (host_gnt     ),
    .host_addr_i         (host_addr    ),
    .host_we_i           (host_we      ),
    .host_be_i           (host_be      ),
    .host_wdata_i        (host_wdata   ),
    .host_rvalid_o       (host_rvalid  ),
    .host_rdata_o        (host_rdata   ),
    .host_err_o          (host_err     ),

    .device_req_o        (device_req   ),
    .device_addr_o       (device_addr  ),
    .device_we_o         (device_we    ),
    .device_be_o         (device_be    ),
    .device_wdata_o      (device_wdata ),
    .device_rvalid_i     (device_rvalid),
    .device_rdata_i      (device_rdata ),
    .device_err_i        (device_err   ),

    .cfg_device_addr_base,
    .cfg_device_addr_mask
  );

  logic [31:0] bus2cfgbase [1];
  logic [31:0] bus2cfgmask [1];

  assign bus2cfgbase[0] = cfg_device_addr_base[Ram];
  assign bus2cfgmask[0] = cfg_device_addr_mask[Ram];

  bus #(
    .NrDevices    ( 1 ),
    .NrHosts      ( NrHosts   ),
    .DataWidth    ( 32        ),
    .AddressWidth ( 32        )
  ) u_bus2 (
    .clk_i               (clk_sys),
    .rst_ni              (rst_sys_n),

    .host_req_i          (instr_req     ),
    .host_gnt_o          (instr_gnt     ),
    .host_addr_i         (instr_addr    ),
    .host_we_i           (      ),
    .host_be_i           (     ),
    .host_wdata_i        (   ),
    .host_rvalid_o       (instr_rvalid  ),
    .host_rdata_o        (instr_rdata   ),
    .host_err_o          (     ),

    .device_req_o        (ram_instr_req   ),
    .device_addr_o       (ram_instr_addr  ),
    .device_we_o         (    ),
    .device_be_o         (   ),
    .device_wdata_o      ( ),
    .device_rvalid_i     (ram_instr_rvalid),
    .device_rdata_i      (ram_instr_rdata ),
    .device_err_i        (  ),

    .cfg_device_addr_base(bus2cfgbase),
    .cfg_device_addr_mask(bus2cfgmask)
  );



genvar i;

generate
    if (SecureIbex) begin : g_mem_rdata_ecc
    logic [31:0] unused_data_rdata;
    logic [31:0] unused_instr_rdata;
  for (i = 0; i < NrHosts; i++) begin
    prim_secded_inv_39_32_enc u_data_rdata_intg_gen (
      .data_i(host_rdata[i]),
      .data_o({data_rdata_intg[i], unused_data_rdata})
    );

    prim_secded_inv_39_32_enc u_instr_rdata_intg_gen (
      .data_i(instr_rdata[i]),
      .data_o({instr_rdata_intg[i], unused_instr_rdata})
    );
  end
      end else begin : g_no_mem_rdata_ecc

          assign data_rdata_intg = '0;
    assign instr_rdata_intg = '0;
  end

  
endgenerate
/*
    prim_secded_inv_39_32_enc u_data_rdata_intg1_gen (
      .data_i (host_rdata[CoreD]),
      .data_o ({data_rdata_intg1, unused_data_rdata})
    );

    prim_secded_inv_39_32_enc u_data_rdata_intg2_gen (
      .data_i (host_rdata[CoreE]),
      .data_o ({data_rdata_intg2, unused_data_rdata})
    );

    prim_secded_inv_39_32_enc u_instr_rdata_intg1_gen (
      .data_i (instr_rdata1),
      .data_o ({instr_rdata_intg1, unused_instr_rdata})
    );

    prim_secded_inv_39_32_enc u_instr_rdata_intg2_gen (
      .data_i (instr_rdata2),
      .data_o ({instr_rdata_intg2, unused_instr_rdata})
    );
    */
  /*
    assign data_rdata_intg1 = '0;
    assign instr_rdata_intg1 = '0;
    assign data_rdata_intg2 = '0;
    assign instr_rdata_intg2 = '0;
    */



generate
  for (i = 0; i < NrHosts; i++) begin
    ibex_top_tracing #(
      .SecureIbex      ( SecureIbex       ),
      .ICacheScramble  ( ICacheScramble   ),
      .PMPEnable       ( PMPEnable        ),
      .PMPGranularity  ( PMPGranularity   ),
      .PMPNumRegions   ( PMPNumRegions    ),
      .MHPMCounterNum  ( MHPMCounterNum   ),
      .MHPMCounterWidth( MHPMCounterWidth ),
      .RV32E           ( RV32E            ),
      .RV32M           ( RV32M            ),
      .RV32B           ( RV32B            ),
      .RegFile         ( RegFile          ),
      .BranchTargetALU ( BranchTargetALU  ),
      .ICache          ( ICache           ),
      .ICacheECC       ( ICacheECC        ),
      .WritebackStage  ( WritebackStage   ),
      .BranchPredictor ( BranchPredictor  ),
      .DbgTriggerEn    ( DbgTriggerEn     ),
      //.DmBaseAddr      ( 32'h00100000 + ((32'hFFFFF)/NrHosts)*i  ), //
      .DmBaseAddr(32'h00100000),
      .DmAddrMask      ( 32'h00000003     ),
      //.DmHaltAddr      ( 32'h00100000 + ((32'hFFFFF)/NrHosts)*i  ), //
      .DmHaltAddr(32'h00100000),
      //.DmExceptionAddr ( 32'h00100000 + ((32'hFFFFF)/NrHosts)*i  ) //
      .DmExceptionAddr(32'h00100000)
    ) u_top (
      .clk_i                  (clk_sys),
      .rst_ni                 (rst_sys_n),

      .test_en_i              (1'b0),
      .scan_rst_ni            (1'b1),
      .ram_cfg_i              (prim_ram_1p_pkg::RAM_1P_CFG_DEFAULT),

      .hart_id_i              (i),
      // First instruction executed is at 0x0 + 0x80
      //.boot_addr_i            (32'h00100000 + (((32'hFFFFF) + 1)/NrHosts)*i), // technically includes 200000, one bad addr
      .boot_addr_i(32'h00100000),

      .instr_req_o            (instr_req[i]),
      .instr_gnt_i            (instr_gnt[i]),
      .instr_rvalid_i         (instr_rvalid[i]),
      .instr_addr_o           (instr_addr[i]),
      .instr_rdata_i          (instr_rdata[i]),
      .instr_rdata_intg_i     (instr_rdata_intg[i]),
      //.instr_err_i            (instr_err[i]),
      .instr_err_i (),

      .data_req_o             (host_req[i]),
      .data_gnt_i             (host_gnt[i]),
      .data_rvalid_i          (host_rvalid[i]),
      .data_we_o              (host_we[i]),
      .data_be_o              (host_be[i]),
      .data_addr_o            (host_addr[i]),
      .data_wdata_o           (host_wdata[i]),
      .data_wdata_intg_o      (),
      .data_rdata_i           (host_rdata[i]),
      .data_rdata_intg_i      (data_rdata_intg[i]),
      .data_err_i             (host_err[i]),
      .input_valid(valid_i[i]),
      .input_addr(addr_i[i]),
      .input_data(data_i[i]),
      .output_valid(valid_o[i]),
      .output_data(data_o[i]),
      .output_addr(addr_o[i]),
      .len_i(len_i[i]),
      .len_o(len_o[i]),
      .msg1_data(msg1_data[i]),
      .msg2_data(msg2_data[i]),
      .msg3_data(msg3_data[i]),
      .msg1_data_i(msg1_data_i[i]),
      .msg2_data_i(msg2_data_i[i]),
      .msg3_data_i(msg3_data_i[i]),

      .irq_software_i         (1'b0),
      .irq_timer_i            (timer_irq),
      .irq_external_i         (1'b0),
      .irq_fast_i             (15'b0),
      .irq_nm_i               (1'b0),

      .scramble_key_valid_i   ('0),
      .scramble_key_i         ('0),
      .scramble_nonce_i       ('0),
      .scramble_req_o         (),

      .debug_req_i            (1'b0),
      .crash_dump_o           (),
      .double_fault_seen_o    (),

      .fetch_enable_i         (ibex_pkg::IbexMuBiOn),
      .alert_minor_o          (),
      .alert_major_internal_o (),
      .alert_major_bus_o      (),
      .core_sleep_o           ()
    );
  end
endgenerate

/*
  ibex_top_tracing #(
      .SecureIbex      ( SecureIbex       ),
      .ICacheScramble  ( ICacheScramble   ),
      .PMPEnable       ( PMPEnable        ),
      .PMPGranularity  ( PMPGranularity   ),
      .PMPNumRegions   ( PMPNumRegions    ),
      .MHPMCounterNum  ( MHPMCounterNum   ),
      .MHPMCounterWidth( MHPMCounterWidth ),
      .RV32E           ( RV32E            ),
      .RV32M           ( RV32M            ),
      .RV32B           ( RV32B            ),
      .RegFile         ( RegFile          ),
      .BranchTargetALU ( BranchTargetALU  ),
      .ICache          ( ICache           ),
      .ICacheECC       ( ICacheECC        ),
      .WritebackStage  ( WritebackStage   ),
      .BranchPredictor ( BranchPredictor  ),
      .DbgTriggerEn    ( DbgTriggerEn     ),
      .DmBaseAddr      ( 32'h00100000     ),
      .DmAddrMask      ( 32'h00000003     ),
      .DmHaltAddr      ( 32'h00100000     ),
      .DmExceptionAddr ( 32'h00100000     )
    ) u_top1 (
      .clk_i                  (clk_sys),
      .rst_ni                 (rst_sys_n),

      .test_en_i              (1'b0),
      .scan_rst_ni            (1'b1),
      .ram_cfg_i              (prim_ram_1p_pkg::RAM_1P_CFG_DEFAULT),

      .hart_id_i              (32'b0),
      // First instruction executed is at 0x0 + 0x80
      .boot_addr_i            (32'h00100000),

      .instr_req_o            (instr_req1),
      .instr_gnt_i            (instr_gnt1),
      .instr_rvalid_i         (instr_rvalid1),
      .instr_addr_o           (instr_addr1),
      .instr_rdata_i          (instr_rdata1),
      .instr_rdata_intg_i     (instr_rdata_intg1),
      .instr_err_i            (instr_err1),

      .data_req_o             (host_req[CoreD]),
      .data_gnt_i             (host_gnt[CoreD]),
      .data_rvalid_i          (host_rvalid[CoreD]),
      .data_we_o              (host_we[CoreD]),
      .data_be_o              (host_be[CoreD]),
      .data_addr_o            (host_addr[CoreD]),
      .data_wdata_o           (host_wdata[CoreD]),
      .data_wdata_intg_o      (),
      .data_rdata_i           (host_rdata[CoreD]),
      .data_rdata_intg_i      (data_rdata_intg1),
      .data_err_i             (host_err[CoreD]),
      .input_valid(valid10),
      .input_addr(addr10),
      .input_data(data10),
      .output_valid(valid01),
      .output_data(data01),
      .output_addr(addr01),

      .irq_software_i         (1'b0),
      .irq_timer_i            (timer_irq),
      .irq_external_i         (1'b0),
      .irq_fast_i             (15'b0),
      .irq_nm_i               (1'b0),

      .scramble_key_valid_i   ('0),
      .scramble_key_i         ('0),
      .scramble_nonce_i       ('0),
      .scramble_req_o         (),

      .debug_req_i            (1'b0),
      .crash_dump_o           (),
      .double_fault_seen_o    (),

      .fetch_enable_i         (ibex_pkg::IbexMuBiOn),
      .alert_minor_o          (),
      .alert_major_internal_o (),
      .alert_major_bus_o      (),
      .core_sleep_o           ()
    );
*/
/*
      ibex_top_tracing #(
      .SecureIbex      ( SecureIbex       ),
      .ICacheScramble  ( ICacheScramble   ),
      .PMPEnable       ( PMPEnable        ),
      .PMPGranularity  ( PMPGranularity   ),
      .PMPNumRegions   ( PMPNumRegions    ),
      .MHPMCounterNum  ( MHPMCounterNum   ),
      .MHPMCounterWidth( MHPMCounterWidth ),
      .RV32E           ( RV32E            ),
      .RV32M           ( RV32M            ),
      .RV32B           ( RV32B            ),
      .RegFile         ( RegFile          ),
      .BranchTargetALU ( BranchTargetALU  ),
      .ICache          ( ICache           ),
      .ICacheECC       ( ICacheECC        ),
      .WritebackStage  ( WritebackStage   ),
      .BranchPredictor ( BranchPredictor  ),
      .DbgTriggerEn    ( DbgTriggerEn     ),
      .DmBaseAddr      ( 32'h00300000     ),
      .DmAddrMask      ( 32'h00000003     ),
      .DmHaltAddr      ( 32'h00300000     ),
      .DmExceptionAddr ( 32'h00300000     )
    ) u_top2 (
      .clk_i                  (clk_sys),
      .rst_ni                 (rst_sys_n),

      .test_en_i              (1'b0),
      .scan_rst_ni            (1'b1),
      .ram_cfg_i              (prim_ram_1p_pkg::RAM_1P_CFG_DEFAULT),

      .hart_id_i              (32'b1),
      // First instruction executed is at 0x0 + 0x80
      .boot_addr_i            (32'h00300000),

      .instr_req_o            (instr_req2),
      .instr_gnt_i            (instr_gnt2),
      .instr_rvalid_i         (instr_rvalid2),
      .instr_addr_o           (instr_addr2),
      .instr_rdata_i          (instr_rdata2),
      .instr_rdata_intg_i     (instr_rdata_intg2),
      .instr_err_i            (instr_err2),

      .data_req_o             (host_req[CoreE]),
      .data_gnt_i             (host_gnt[CoreE]),
      .data_rvalid_i          (host_rvalid[CoreE]),
      .data_we_o              (host_we[CoreE]),
      .data_be_o              (host_be[CoreE]),
      .data_addr_o            (host_addr[CoreE]),
      .data_wdata_o           (host_wdata[CoreE]),
      .data_wdata_intg_o      (),
      .data_rdata_i           (host_rdata[CoreE]),
      .data_rdata_intg_i      (data_rdata_intg2),
      .data_err_i             (host_err[CoreE]),

      .input_valid(valid01),
      .input_addr(addr01),
      .input_data(data01),
      .output_valid(valid10),
      .output_data(data10),
      .output_addr(addr10),

      .irq_software_i         (1'b0),
      .irq_timer_i            (timer_irq),
      .irq_external_i         (1'b0),
      .irq_fast_i             (15'b0),
      .irq_nm_i               (1'b0),

      .scramble_key_valid_i   ('0),
      .scramble_key_i         ('0),
      .scramble_nonce_i       ('0),
      .scramble_req_o         (),

      .debug_req_i            (1'b0),
      .crash_dump_o           (),
      .double_fault_seen_o    (),

      .fetch_enable_i         (ibex_pkg::IbexMuBiOn),
      .alert_minor_o          (),
      .alert_major_internal_o (),
      .alert_major_bus_o      (),
      .core_sleep_o           ()
    );
    */

  // SRAM block for instruction and data storage
  ram_2p #(
      .Depth(1024*1024/4),
      .MemInitFile(SRAMInitFile)
    ) u_ram (
      .clk_i       (clk_sys),
      .rst_ni      (rst_sys_n),

      .a_req_i     (device_req[Ram]),
      .a_we_i      (device_we[Ram]),
      .a_be_i      (device_be[Ram]),
      .a_addr_i    (device_addr[Ram]),
      .a_wdata_i   (device_wdata[Ram]),
      .a_rvalid_o  (device_rvalid[Ram]),
      .a_rdata_o   (device_rdata[Ram]),

      .b_req_i     (ram_instr_req[0]), // need to find way to figure this out
      .b_we_i      (1'b0),
      .b_be_i      (4'b0),
      .b_addr_i    (ram_instr_addr[0]),
      .b_wdata_i   (32'b0),
      .b_rvalid_o  (ram_instr_rvalid[0]),
      .b_rdata_o   (ram_instr_rdata[0])
    );

/*
     ram_2p #(
      .Depth(1024*1024/4),
      .MemInitFile(SRAMInitFile)
    ) u_ram2 (
      .clk_i       (clk_sys),
      .rst_ni      (rst_sys_n),

      .a_req_i     (device_req[Ram2]),
      .a_we_i      (device_we[Ram2]),
      .a_be_i      (device_be[Ram2]),
      .a_addr_i    (device_addr[Ram2]),
      .a_wdata_i   (device_wdata[Ram2]),
      .a_rvalid_o  (device_rvalid[Ram2]),
      .a_rdata_o   (device_rdata[Ram2]),

      .b_req_i     (instr_req2),
      .b_we_i      (1'b0),
      .b_be_i      (4'b0),
      .b_addr_i    (instr_addr2),
      .b_wdata_i   (32'b0),
      .b_rvalid_o  (instr_rvalid2),
      .b_rdata_o   (instr_rdata2)
    );
    */

  simulator_ctrl #(
    .LogName("ibex_multicore_system.log")
    ) u_simulator_ctrl (
      .clk_i     (clk_sys),
      .rst_ni    (rst_sys_n),

      .req_i     (device_req[SimCtrl]),
      .we_i      (device_we[SimCtrl]),
      .be_i      (device_be[SimCtrl]),
      .addr_i    (device_addr[SimCtrl]),
      .wdata_i   (device_wdata[SimCtrl]),
      .rvalid_o  (device_rvalid[SimCtrl]),
      .rdata_o   (device_rdata[SimCtrl])
    );

  timer #(
    .DataWidth    (32),
    .AddressWidth (32)
    ) u_timer (
      .clk_i          (clk_sys),
      .rst_ni         (rst_sys_n),

      .timer_req_i    (device_req[Timer]),
      .timer_we_i     (device_we[Timer]),
      .timer_be_i     (device_be[Timer]),
      .timer_addr_i   (device_addr[Timer]),
      .timer_wdata_i  (device_wdata[Timer]),
      .timer_rvalid_o (device_rvalid[Timer]),
      .timer_rdata_o  (device_rdata[Timer]),
      .timer_err_o    (device_err[Timer]),
      .timer_intr_o   (timer_irq)
    );

  export "DPI-C" function mhpmcounter_num;

  function automatic int unsigned mhpmcounter_num();
    //return u_top[0].u_ibex_top.u_ibex_core.cs_registers_i.MHPMCounterNum; // what is this, is this correct to put the 1?
    return 0;
  endfunction

  export "DPI-C" function mhpmcounter_get;

  function automatic longint unsigned mhpmcounter_get(int index);
    //return u_top[0].u_ibex_top.u_ibex_core.cs_registers_i.mhpmcounter[index]; // what is this, is this correct to put the 1?
    return 0;
  endfunction

endmodule
