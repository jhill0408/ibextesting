`include "mux.h"

module pi_route #(
	parameter N	= 8,		// number of clients
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
	input  wire u1_i_v,		// up1 input valid
	input  wire l_i_defl,		// left input is a deflected packet
	input  wire r_i_defl,		// right input is a deflected packet
	input  wire u0_i_defl,		// up0 input is a deflected packet
	input  wire u1_i_defl,		// up1 input is a deflected packet
	input  wire [A_W-1:0] l_i_addr,	// left input addr
	input  wire [A_W-1:0] r_i_addr,	// right input addr
	input  wire [A_W-1:0] u0_i_addr, // up0 input addr
	input  wire [A_W-1:0] u1_i_addr, // up0 input addr
	output wire l_o_v,		// valid for l mux
	output wire r_o_v,		// valid for r mux
	output wire u0_o_v,		// valid for u0 mux
	output wire u1_o_v,		// valid for u1 mux
	output wire l_o_defl,		// left output is a deflected packet
	output wire r_o_defl,		// right output is a deflected packet
	output wire u0_o_defl,		// up0 output is a deflected packet
	output wire u1_o_defl,		// up1 output is a deflected packet
	output wire [2:0] l_sel,	// select for l mux
	output wire [2:0] r_sel,	// select for r mux
	output wire [2:0] u0_sel,	// select for u0 mux
	output wire [2:0] u1_sel	// select for u1 mux
);

	wire [A_W-1:0] l_o_addr;	// left input addr
	wire [A_W-1:0] r_o_addr;	// right input addr
	wire [A_W-1:0] u0_o_addr; 	// up0 input addr
	wire [A_W-1:0] u1_o_addr; 	// up0 input addr

	// signals for storing where to turn...
	wire l_to_r, r_to_l;
	wire l_to_u, r_to_u;
	wire u0_to_l, u0_to_r;
	wire u1_to_l, u1_to_r;
	wire l_to_l, r_to_r, u0_to_u0, u1_to_u1;

	assign l_to_r = l_i_v & l_i_addr[posl] & l_i_addr[A_W-1:posl+1]==posx[A_W-1:posl];
	assign l_to_u = l_i_v & l_i_addr[A_W-1:posl+1]!=posx[A_W-1:posl];
	assign r_to_l = r_i_v & ~r_i_addr[posl] & r_i_addr[A_W-1:posl+1]==posx[A_W-1:posl];
	assign r_to_u = r_i_v & r_i_addr[A_W-1:posl+1]!=posx[A_W-1:posl];
	assign u0_to_l = ~u0_i_defl & u0_i_v & ~u0_i_addr[posl];
	assign u0_to_r = ~u0_i_defl & u0_i_v & u0_i_addr[posl];
	assign u1_to_l = ~u1_i_defl & u1_i_v & ~u1_i_addr[posl];
	assign u1_to_r = ~u1_i_defl & u1_i_v & u1_i_addr[posl];

	assign l_to_l = l_i_v & l_i_defl;
	assign r_to_r = r_i_v & r_i_defl;
	assign u0_to_u0 = u0_i_v & u0_i_defl;
	assign u1_to_u1 = u1_i_v & u1_i_defl;

	// triangle exception
	wire triangle_exception_u0;
	wire triangle_exception_u1;
	//assign triangle_exception = 0;
	assign triangle_exception_u0 = (1'b0 |
		l_to_r & r_to_u & u0_to_l & (u1_to_u1 | u1_to_l) | 
		r_to_l & l_to_u & u0_to_r & (u1_to_u1 | u1_to_r) | 
		1'b0);
	assign triangle_exception_u1 = (1'b0 |
		l_to_r & r_to_u & u1_to_l & (u0_to_u0 | ~u0_to_l) | 
		r_to_l & l_to_u & u1_to_r & (u0_to_u0 | ~u0_to_r) | 
		1'b0);

		assign l_sel = (l_o_defl | l_to_l)? `LEFT: 
				(r_to_l & ~r_o_defl) ? `RIGHT : 
				(u0_to_l & ~u0_o_defl & ~u0_to_u0) ? `U0 : 
				(u1_to_l & ~u1_o_defl & ~u1_to_u1) ? `U1 : `NONE;

		assign l_o_v = (l_o_defl | l_to_l)? 1: 
				(r_to_l & ~r_o_defl)? 1 : 
				(u0_to_l & ~u0_o_defl & ~u0_to_u0) ? 1 :
				(u1_to_l & ~u1_o_defl & ~u1_to_u1) ? 1 : 0;

		assign l_o_addr = (l_sel==`RIGHT)? r_i_addr : 
					(l_sel==`U0)? u0_i_addr:
					(l_sel==`U1)? u1_i_addr:0;

		assign r_sel = (r_o_defl | r_to_r)? `RIGHT: 
				(l_to_r & ~l_o_defl)? `LEFT : 
				(u0_to_r & ~u0_o_defl & ~u0_to_u0) ? `U0 :
				(u1_to_r & ~u1_o_defl & ~u1_to_u1) ? `U1 : `NONE;

		assign r_o_v = (r_o_defl | r_to_r)? 1: 
				(l_to_r & ~l_o_defl)? 1 : 
				(u0_to_r & ~u0_o_defl & ~u0_to_u0) ? 1 :
				(u1_to_r & ~u1_o_defl & ~u1_to_u1) ? 1 : 0;

		assign r_o_addr = (r_sel==`LEFT)? l_i_addr:
				(r_sel==`U0)? u0_i_addr:
				(r_sel==`U1)? u1_i_addr:0;

		assign u0_sel = (u0_o_defl | u0_to_u0)? `U0: 
				(l_to_u & ~l_o_defl)? `LEFT : 
				(r_to_u & ~r_o_defl)? `RIGHT: `NONE;	

		assign u0_o_v = (u0_o_defl | u0_to_u0)? 1 : 
				(l_to_u & ~l_o_defl)? 1 : 
				(r_to_u & ~r_o_defl & (u1_o_defl | u1_to_u1))? 1 : 0;

		assign u0_o_addr = (u0_sel==`LEFT)? l_i_addr : 
				(u0_sel==`RIGHT)?r_i_addr : 
				(u0_sel==`U0)?u0_i_addr:0;
		
		assign u1_sel = (u1_o_defl | u1_to_u1)? `U1: 
				(r_to_u & ~r_o_defl)? `RIGHT: 
				(l_to_u & ~l_o_defl & (u0_o_defl | u0_to_u0))? `LEFT : `NONE;	

		assign u1_o_v = (u1_o_defl | u1_to_u1)? 1 : 
				(l_to_u & ~l_o_defl & (u0_o_defl | u0_to_u0))? 1 : 
				(r_to_u & ~r_o_defl)? 1 : 0;	

		assign u1_o_addr = (u1_sel==`LEFT)? l_i_addr : 
				(u1_sel==`RIGHT)?r_i_addr : 
				(u1_sel==`U1)?u1_i_addr:0;
		
		assign l_o_defl = 1'b0 | 
			~l_to_l&~(triangle_exception_u0|triangle_exception_u1)&
			( 
			  ((u0_to_r | u0_to_u0) & (u1_to_r | u1_to_u1) & l_to_u & r_to_u)  |
			  (u0_to_u0 & u1_to_u1 & l_to_u )  |
			  (u0_to_u0 & u1_to_u1 & l_to_u & r_to_u)  |
			  (u0_to_u0 & ~u1_i_v  & l_to_u & r_to_u & toggle)  |
			  (u1_to_u1 & ~u0_i_v  & l_to_u & r_to_u & toggle)  |
                          (l_to_u   & r_to_r & u0_to_r & u1_to_r)  |
			  (r_to_l   & l_to_u  & (u1_to_r | u1_to_u1) & u0_to_u0) |
			  (r_to_l   & l_to_u  & (u0_to_r | u0_to_u0) & u1_to_u1) |
			  (r_to_u   & l_to_r  & (u1_to_l | u1_to_u1) & u0_to_u0) |
			  (r_to_u   & l_to_r  & (u0_to_l | u0_to_u0) & u1_to_u1) |
			  (r_to_r   & l_to_r)  |
			  (r_to_r   & u1_to_u1 & l_to_u & u0_to_r)  | 
			  (r_to_r   & u0_to_u0 & l_to_u & u1_to_r)  | 
			  (l_to_r   & (u0_to_r | u1_to_r) & r_to_u) |
			  (u0_to_u0 & u1_to_u1 & & r_to_u & l_to_r) |
			  1'd0);

		assign r_o_defl = 1'b0 | 
			~r_to_r&~(triangle_exception_u0|triangle_exception_u1)&
			( 
			  ((u0_to_l | u0_to_u0) & (u1_to_l | u1_to_u1) & l_to_u & r_to_u )  |
			  (u0_to_u0 & u1_to_u1 & r_to_u )  |
			  (u0_to_u0 & u1_to_u1 & l_to_u & r_to_u)  |
			  (u0_to_u0 & ~u1_i_v  & l_to_u & r_to_u & ~toggle)  |
			  (u1_to_u1 & ~u0_i_v  & l_to_u & r_to_u & ~toggle)  |
                          (r_to_u   & l_to_l & u0_to_l & u1_to_l)  |
			  (l_to_l   & r_to_l)  | 
			  (l_to_l   & u1_to_u1 & r_to_u & u0_to_l)  | 
			  (l_to_l   & u0_to_u0 & r_to_u & u1_to_l)  | 
			  (r_to_l   & l_to_u  & (u1_to_r | u1_to_u1) & u0_to_u0) |
			  (r_to_l   & l_to_u  & (u0_to_r | u0_to_u0) & u1_to_u1) |
			  (r_to_u   & l_to_r  & (u1_to_l | u1_to_u1) & u0_to_u0) |
			  (r_to_u   & l_to_r  & (u0_to_l | u0_to_u0) & u1_to_u1) |
			  (r_to_l   & (u0_to_l | u1_to_l) & l_to_u) |
			  (u0_to_u0 & u1_to_u1 & l_to_u & r_to_l)  |
			  1'b0);

		assign u0_o_defl = 1'b0 | 
			~u0_to_u0&~triangle_exception_u0&
			( (r_to_l   & l_to_r  & (u0_to_l | u0_to_r)) |
			  (u0_to_l  & u1_to_l & (l_i_v & ~r_i_v | ~l_i_v & r_i_v | ~l_i_v & ~r_i_v | (r_to_l|r_to_r) & l_to_u) & toggle)  |
			  (u0_to_r  & u1_to_r & (l_i_v & ~r_i_v | ~l_i_v & r_i_v | ~l_i_v & ~r_i_v | (l_to_r|l_to_l) & r_to_u) & toggle)  |
			  (triangle_exception_u1 & (u0_to_l|u0_to_r)) |
			  (u0_to_l  & u1_to_l & (l_to_u & r_to_u)  & toggle)  |
			  (u0_to_r  & u1_to_r & (l_to_u & r_to_u)  & toggle)  |
			  (u0_to_l  & l_to_l) |
			  (u0_to_r  & r_to_r) |
			  (u0_to_l  & r_to_r  & l_to_r) |
			  (u0_to_r  & l_to_l  & r_to_l) |
			  (r_to_l   & l_to_u  & u0_to_r & u1_to_l) |
			  (r_to_u   & l_to_r  & u1_to_r & u0_to_l) |
			  (r_to_l   & l_to_u  & u0_to_r & u1_to_u1) |
			  (r_to_u   & l_to_r  & u0_to_l & u1_to_u1) |
			  (r_to_l   & u0_to_l & ~l_to_u) |
			  (l_to_r   & u0_to_r & ~r_to_u) |
			  1'b0);
	
		assign u1_o_defl = 1'b0 | 
			~u1_to_u1&~triangle_exception_u1&
			( (r_to_l   & l_to_r  & (u1_to_l | u1_to_r)) |
			  (u0_to_l  & u1_to_l & (l_i_v & ~r_i_v | ~l_i_v & r_i_v | ~l_i_v & ~r_i_v | (r_to_l|r_to_r) & l_to_u ) & ~toggle)  |
			  (u0_to_r  & u1_to_r & (l_i_v & ~r_i_v | ~l_i_v & r_i_v | ~l_i_v & ~r_i_v | (l_to_r|l_to_l) & r_to_u) & ~toggle)  |
			  (triangle_exception_u0 & (u1_to_l|u1_to_r)) |
			  (u0_to_l  & u1_to_l & (l_to_u & r_to_u)  & ~toggle)  |
			  (u0_to_r  & u1_to_r & (l_to_u & r_to_u)  & ~toggle)  |
			  (u1_to_l  & l_to_l) |
			  (u1_to_r  & r_to_r) |
			  (u1_to_l  & r_to_r  & l_to_r) |
			  (u1_to_r  & l_to_l  & r_to_l) |
			  (r_to_l   & l_to_u  & u1_to_r & u0_to_l) |
			  (r_to_u   & l_to_r  & u0_to_r & u1_to_l) |
			  (r_to_l   & l_to_u  & u1_to_r & u0_to_u0) |
			  (r_to_u   & l_to_r  & u1_to_l & u0_to_u0) |
			  (r_to_l   & u1_to_l & ~l_to_u) |
			  (l_to_r   & u1_to_r & ~r_to_u) |
			  1'b0);
	
	reg toggle;
	always @(posedge clk) begin
		if(rst) begin
			toggle <=0;
		end else begin
			toggle <= ~toggle;
		end
	end


endmodule


