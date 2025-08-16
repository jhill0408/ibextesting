/* verilator lint_off DECLFILENAME */
module Mux2 #(
	parameter W = 32
) (
	input wire s,
	input wire [W-1:0] i0,
	input wire [W-1:0] i1,
	output wire [W-1:0] o
);
	assign o = s ? i1 : i0;
endmodule


module Mux3 #(
	parameter W = 32
) (
	input wire [1:0] s,
	input wire [W-1:0] i0,
	input wire [W-1:0] i1,
	input wire [W-1:0] i2,
	output wire [W-1:0] o
);
	assign o = s[1] ? i2 : s[0] ? i1 : i0;
endmodule


module Mux4 #(
	parameter W = 32
) (
	input wire [1:0] s,
	input wire [W-1:0] i0,
	input wire [W-1:0] i1,
	input wire [W-1:0] i2,
	input wire [W-1:0] i3,
	output wire [W-1:0] o
);
	assign o = s[1] ? (s[0]? i3 : i2) : (s[0] ? i1 : i0);
endmodule

