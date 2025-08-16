`include "mux.h"

module pi_route_lean #(
	parameter N	= 8,		// number of clients
	parameter LEVELS= $clog2(N),	// number of levels
	parameter A_W	= $clog2(N)+1,	// log number of clients
	parameter posl  = 0,		// which level
	parameter posx 	= 0		// which position
) (
	input  wire clk,		// clock
	input  wire rst,		// reset
	input  wire ce,			// clock enable
	input  wire l_i_v,		// left input valid
	input  wire r_i_v,		// right input valid
	input  wire u0_i_v,		// up0 input valid
	input  wire u1_i_v,		// up0 input valid
	input  wire l_i_defl,		// left input is a deflected packet
	input  wire r_i_defl,		// right input is a deflected packet
	input  wire u0_i_defl,		// up0 input is a deflected packet
	input  wire u1_i_defl,		// up0 input is a deflected packet
	input  wire [A_W-1:0] l_i_addr,	// left input addr
	input  wire [A_W-1:0] r_i_addr,	// right input addr
	input  wire [A_W-1:0] u0_i_addr, // up0 input addr
	input  wire [A_W-1:0] u1_i_addr, // up0 input addr
	output wire l_o_v,		// valid for l mux
	output wire r_o_v,		// valid for r mux
	output wire u0_o_v,		// valid for u0 mux
	output wire u1_o_v,		// valid for u0 mux
	output wire l_o_defl,		// left output is a deflected packet
	output wire r_o_defl,		// right output is a deflected packet
	output wire u0_o_defl,		// up0 output is a deflected packet
	output wire u1_o_defl,		// up0 output is a deflected packet
	output wire [2:0] l_sel,	// select for l mux
	output wire [2:0] r_sel,	// select for r mux
	output wire [2:0] u0_sel,	// select for u0 mux
	output wire [2:0] u1_sel	// select for u0 mux
);

	// signals for storing where to turn...
	wire l_to_r, r_to_l;
	wire l_to_u, r_to_u;
	wire u0_to_l, u0_to_r;
	wire u1_to_l, u1_to_r;
	
	assign l_to_r = l_i_v & l_i_addr[posl] & l_i_addr[A_W-1:posl+1]==posx[A_W-1:posl];
	assign l_to_u = l_i_v & l_i_addr[A_W-1:posl+1]!=posx[A_W-1:posl];
	assign r_to_l = r_i_v & ~r_i_addr[posl] & r_i_addr[A_W-1:posl+1]==posx[A_W-1:posl];
	assign r_to_u = r_i_v & r_i_addr[A_W-1:posl+1]!=posx[A_W-1:posl];
	assign u0_to_l = u0_i_v & ~u0_i_addr[posl];
	assign u0_to_r = u0_i_v & u0_i_addr[posl];
	assign u1_to_l = u1_i_v & ~u1_i_addr[posl];
	assign u1_to_r = u1_i_v & u1_i_addr[posl];

	//wire l_to_wrap = 0;
	//wire r_to_wrap = 0;
	wire l_to_wrap = l_i_v & ~l_i_addr[posl] & l_i_addr[A_W-1:posl+1]==posx[A_W-1:posl];// & posl==A_W-2;
	wire r_to_wrap = r_i_v & r_i_addr[posl] & r_i_addr[A_W-1:posl+1]==posx[A_W-1:posl];// & posl==A_W-2;
	always @(posedge clk) begin
		if(l_to_wrap | r_to_wrap) begin
			$display("L or R wrap observed...");
		end
	end

	wire defl_r_u0 = r_to_l&u0_to_l&~u1_to_r&~u1_to_l&~l_to_r;
	wire defl_l_u0 = l_to_r&u0_to_r&~u1_to_l&~u1_to_r&~r_to_l;
	wire defl_r_u1 = r_to_l&u1_to_l&~u0_to_l&~l_to_r;
	wire defl_l_u1 = l_to_r&u1_to_r&~u0_to_r&~r_to_l;
	wire defl_u0u1_l2r = l_to_r&u1_to_l&u0_to_l;
	wire defl_u0u1_r2l = r_to_l&u1_to_r&u0_to_r;
	wire defl_ru0u1 = r_to_l&u1_to_l&u0_to_l;
	wire defl_lu0u1 = l_to_r&u1_to_r&u0_to_r;
	wire defl_u0u1_to_r = u1_to_r&u0_to_r;
	wire defl_u0u1_to_l = u1_to_l&u0_to_l;
	wire defl_l_ru = l_to_r & r_to_l & (u0_to_r | u1_to_r);
	wire defl_r_lu = l_to_r & r_to_l & (u0_to_l | u1_to_l);

	assign l_sel = ~(u0_i_v&u1_i_v)&(r_to_l&~u0_to_l&~u1_to_l&~(defl_lu0u1)&~(u0_i_v&u1_i_v) | defl_r_u0 | defl_r_u1)? `RIGHT : 
		(u0_to_l&~defl_ru0u1 | defl_l_u0 | defl_lu0u1) ? `U0 : 
		(u1_to_l | defl_l_u1 | defl_ru0u1 | defl_u0u1_to_r) ? `U1 : 
		`NONE;
	assign l_o_v = r_to_l&~defl_lu0u1 | u0_to_l | u1_to_l | defl_l_u0 | defl_lu0u1 | defl_l_u1 | defl_ru0u1 | defl_r_u0 | defl_r_u1 | defl_u0u1_to_r;

	assign r_sel = ~(u0_i_v&u1_i_v)&(l_to_r&~u0_to_r&~u1_to_r&~defl_ru0u1&~defl_u0u1_to_l | defl_l_u0 | defl_l_u1)? `LEFT : 
		(u0_to_r&~defl_lu0u1 | defl_r_u0 | defl_ru0u1) ? `U0 : 
		(u1_to_r | defl_r_u1 | defl_lu0u1 | defl_u0u1_to_l) ? `U1 : 
		`NONE;
	assign r_o_v = l_to_r | u0_to_r | u1_to_r | defl_r_u0 | defl_ru0u1 | defl_r_u1 | defl_lu0u1 | defl_l_u0 | defl_l_u1 | defl_u0u1_to_l;

	assign u0_sel = (l_to_u | defl_r_u0&l_to_r | defl_r_u1&l_to_r | defl_ru0u1&l_i_v | defl_lu0u1&l_i_v | defl_l_ru | l_to_wrap | (u0_i_v&u1_i_v&l_i_v))? `LEFT : 
			`NONE;	
	assign u0_o_v = l_to_u | defl_r_u0&l_to_r | defl_r_u1&l_to_r | defl_ru0u1&l_i_v | defl_lu0u1&l_i_v | defl_l_ru | l_to_wrap | (u0_i_v&u1_i_v&l_i_v);
		
	assign u1_sel = (r_to_u | defl_l_u1&r_to_l | defl_l_u0&r_to_l | defl_lu0u1&r_i_v | defl_ru0u1&r_i_v | defl_r_lu | r_to_wrap | (u0_i_v&u1_i_v&r_i_v))? `RIGHT: 
			`NONE;	
	assign u1_o_v = r_to_u | defl_l_u1&r_to_l | defl_l_u0&r_to_l | defl_lu0u1&r_i_v | defl_ru0u1&r_i_v | defl_r_lu | r_to_wrap | (u0_i_v&u1_i_v&r_i_v);

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
	assign u1_o_defl = 0;

endmodule


