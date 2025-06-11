module noc_top #(
    parameter NrHosts = 4

) (
    input logic clk_sys,
    input logic rst_sys_n,
    input logic [37:0] data_full_o [NrHosts],
    input logic noc_req_o [NrHosts],
    output logic noc_gnt_i [NrHosts],
    output logic [37:0] data_full_i [NrHosts],
    input logic [4:0] core_o [NrHosts]

);
 
 
  localparam NUM_CORES = NrHosts;

noc_if #(.VC_W(1), .A_W($clog2(NUM_CORES)+1), .D_W(38))
       leaf_rx_noc_if [NUM_CORES-1:0] ( .clk(clk_sys),
       .rst(~rst_sys_n));   // bundled clock+reset

noc_if #(.VC_W(1), .A_W($clog2(NUM_CORES)+1), .D_W(38))
       leaf_tx_noc_if [NUM_CORES-1:0] ( .clk(clk_sys),
       .rst(~rst_sys_n));   // bundled clock+reset

noc_if #(.VC_W(1), .A_W($clog2(NUM_CORES)+1), .D_W(38))
       root_rx_noc_if ( .clk(clk_sys),
       .rst(~rst_sys_n));   // bundled clock+reset

noc_if #(.VC_W(1), .A_W($clog2(NUM_CORES)+1), .D_W(38))
       root_tx_noc_if ( .clk(clk_sys),
       .rst(~rst_sys_n));   // bundled clock+reset

for (genvar i = 0; i < NUM_CORES; ++i) begin : g_cores
    assign leaf_rx_noc_if[i].packet.payload.data = data_full_o[i][37:0];
    assign leaf_rx_noc_if[i].packet.payload.last = 1'b0;
    assign leaf_rx_noc_if[i].vc_target = noc_req_o[i];
    assign noc_gnt_i[i] = leaf_rx_noc_if[i].vc_credit_gnt; 
    assign leaf_tx_noc_if[i].vc_credit_gnt = 'b1; // maybe????

    assign data_full_i[i][37:0] = leaf_tx_noc_if[i].packet.payload.data;

    /* verilator lint_off WIDTHTRUNC */
    assign leaf_rx_noc_if[i].packet.routeinfo.addr = core_o[i];

    /* verilator lint_on WIDTHTRUNC */
end

    assign root_rx_noc_if.packet.payload.data = 'b0;
    assign root_rx_noc_if.packet.payload.last = 1'b0;
    assign root_rx_noc_if.vc_target = 'b0;
    assign root_tx_noc_if.vc_credit_gnt = 'b0; // this is test, not correct?
    assign root_rx_noc_if.packet.routeinfo.addr = 'b0;




  topology_t_binary_tree # (
    .N(NrHosts),
    .D_W(38),
    .VC_W(1)
  ) u_msg_noc (
    .clk(clk_sys),
    .rst(~rst_sys_n),
    .leaf_rx(leaf_rx_noc_if),
    .leaf_tx(leaf_tx_noc_if),
    .root_rx(root_rx_noc_if),
    .root_tx(root_tx_noc_if)
  );

endmodule

