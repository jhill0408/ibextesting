module shadow_reg_combi 
  #(
    parameter D_W = 32,
    parameter A_W = 32,
    parameter posl = 0,
    parameter posx = 0
  )
  (
    input wire clk, 
    input wire rst, 
    input wire i_v,
    input wire [A_W+D_W:0] i_d, 
    output wire i_b,
    output wire o_v,
    output wire [A_W+D_W:0]  o_d, 
    input wire o_b // unregistered from DOR logic
  );

  // shadow register
  reg s_v_r, o_b_r;
  reg [A_W+D_W:0] s_d_r;
  always @(posedge clk) begin
    if(rst) begin
      o_b_r <= 1'b0;
      s_v_r <= 1'b0;
      s_d_r <= 0; // this reset seems to be the problem for verilator for some reason!
    end else begin
      o_b_r <= o_b;
      if(o_b & !o_b_r & !s_v_r) begin
        s_v_r <= i_v;
        s_d_r <= i_d;
      end else if (!o_b) begin
        s_v_r <= 1'b0;
        //   s_d_r <= 0;/////has not been tested
      end
    end
  end

  assign o_v = (o_b_r)?s_v_r:i_v;
  assign o_d = (o_b_r)?s_d_r:i_d;
  assign i_b = o_b_r; // input backpressure is registered

endmodule 
