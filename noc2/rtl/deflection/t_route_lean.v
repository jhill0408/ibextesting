`include "mux.h"

/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off UNUSEDSIGNAL */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off UNUSEDPARAM */

module t_route_lean #(
	parameter N	= 8,		// number of clients
	parameter LEVELS= 2,		// number of levels
	parameter A_W	= $clog2(N)+1,	// log number of clients
	parameter WRAP	= 1,		// crossbar?
	parameter posl  = 0,		// which level
	parameter posx 	= 0		// which position
) (
	input  wire clk,		// clock
	input  wire rst,		// reset
	input  wire ce,			// clock enable
	input  wire l_i_v,		// left input valid
	input  wire r_i_v,		// right input valid
	input  wire u0_i_v,		// up0 input valid
	input  wire l_i_defl,		// left input is a deflected packet
	input  wire r_i_defl,		// right input is a deflected packet
	input  wire u0_i_defl,		// up0 input is a deflected packet
	input  wire [A_W-1:0] l_i_addr,	// left input addr
	input  wire [A_W-1:0] r_i_addr,	// right input addr
	input  wire [A_W-1:0] u0_i_addr, // up0 input addr
	output wire l_o_v,		// valid for l mux
	output wire r_o_v,		// valid for r mux
	output wire u0_o_v,		// valid for u0 mux
	output wire l_o_defl,		// left output is a deflected packet
	output wire r_o_defl,		// right output is a deflected packet
	output wire u0_o_defl,		// up0 output is a deflected packet
	output wire [2:0] l_sel,	// select for l mux
	output wire [2:0] r_sel,	// select for r mux
	output wire [2:0] u0_sel	// select for u0 mux
);

	// signals for storing where to turn...
	wire l_to_r, r_to_l;
	wire l_to_u, r_to_u;
	wire u0_to_l, u0_to_r;
	wire l_to_wrap, r_to_wrap;
	assign l_to_wrap = l_i_v & ~l_i_addr[posl] & l_i_addr[A_W-1:posl+1]==posx[A_W-1:posl];
	assign r_to_wrap = r_i_v & r_i_addr[posl] & r_i_addr[A_W-1:posl+1]==posx[A_W-1:posl];
	
	assign l_to_r = l_i_v & l_i_addr[posl] & l_i_addr[A_W-1:posl+1]==posx[A_W-1:posl] | l_to_wrap;
	assign l_to_u = l_i_v & l_i_addr[A_W-1:posl+1]!=posx[A_W-1:posl];
	assign r_to_l = r_i_v & ~r_i_addr[posl] & r_i_addr[A_W-1:posl+1]==posx[A_W-1:posl] | r_to_wrap;
	assign r_to_u = r_i_v & r_i_addr[A_W-1:posl+1]!=posx[A_W-1:posl];
	assign u0_to_l = u0_i_v & ~u0_i_addr[posl];
	assign u0_to_r = u0_i_v & u0_i_addr[posl];

	assign l_sel = (u0_to_l) ? `U0 : 
		(r_to_l&~u0_i_v&~l_i_v | 
		l_to_u&r_to_u&~u0_i_v  |
		l_to_u&r_to_u&u0_to_r  |
		l_to_u&r_to_l&~u0_i_v  | 
		l_to_u&r_to_l&u0_to_r  | 
		l_to_r&r_to_u&u0_to_r  | 
		l_to_r&r_to_l&~u0_i_v  |
		l_to_r&r_to_l&u0_to_r  |
		r_to_u&u0_to_r&~l_i_v  |
		r_to_l&u0_to_r&~l_i_v  |
		1'b0)? `RIGHT : 
		`NONE;
	assign l_o_v = l_sel!=`NONE;

	assign r_sel = (u0_to_r) ? `U0 : 
		(l_to_r&~u0_i_v&~r_i_v | 
		l_to_u&r_to_u&u0_to_l  | 
		l_to_u&r_to_l&u0_to_l  | 
		l_to_r&r_to_u&~u0_i_v  | 
		l_to_r&r_to_u&u0_to_l  | 
		l_to_r&r_to_l&~u0_i_v  | 
		l_to_r&r_to_l&u0_to_l  | 
		l_to_r&~r_i_v&u0_to_l  | 
		1'b0)? `LEFT : 
		`NONE;
	assign r_o_v = r_sel!=`NONE;

	assign u0_sel = 
		(l_to_u&~r_i_v&~u0_i_v | 
		l_to_u&r_to_u&~u0_i_v  |
		l_to_u&r_to_u&u0_to_r  |
		l_to_u&r_to_l&~u0_i_v  |
		l_to_u&r_to_l&u0_to_r  |
		l_to_r&r_to_u&u0_to_r  |
		l_to_r&r_to_l&u0_to_r  |
		l_to_u&~r_i_v&u0_to_l  | 
		l_to_u&~r_i_v&u0_to_r |
		l_to_r&~r_i_v&u0_to_r |
		1'b0)? `LEFT : 
		(r_to_u&~l_i_v&~u0_i_v | 
		l_to_u&r_to_u&u0_to_l  |
		l_to_u&r_to_l&u0_to_l  |
		l_to_r&r_to_u&~u0_i_v  |
		l_to_r&r_to_u&u0_to_l  |
		l_to_r&r_to_u&u0_to_l  |
		l_to_r&r_to_l&u0_to_l  |
		r_to_u&u0_to_l&~l_i_v  |
		r_to_l&u0_to_l&~l_i_v  |
		1'b0)? `RIGHT: 
		`NONE;	
	assign u0_o_v = u0_sel!=`NONE;
		
	reg toggle;
	always @(posedge clk) begin
		if(rst) begin
			toggle <=0;
		end else begin
			toggle <= ~toggle;
		end
	end

	assign l_o_defl = 0;
	assign r_o_defl = 0;
	assign u0_o_defl = 0;

endmodule


