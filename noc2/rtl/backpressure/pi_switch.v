
module pi_switch #(
	parameter N	= 4,		// number of clients
	parameter WRAP	= 1,		// crossbar?
	parameter A_W	= $clog2(N)+1,	// addr width
	parameter D_W	= 32,		// data width
	parameter posl  = 0,		// which level
	parameter posx 	= 0		// which position
) (
	input  wire 			clk,		// clock
	input  wire 			rst,		// reset
	input  wire 			ce,			// clock enable
	
	input  	wire	[A_W+D_W:0] 	l_i	,	// left  input payload
	output	wire			l_i_bp	,	// left  input backpressured
	input	wire			l_i_v	,	// left  input valid
	
	input  	wire	[A_W+D_W:0] 	r_i	,	// right input payload
	output	wire			r_i_bp	,	// right input backpressured
	input	wire			r_i_v	,	// right input valid
	
	input  	wire	[A_W+D_W:0] 	u0_i	,	// u0    input payload
	output	wire			u0_i_bp	,	// u0    input backpressured
	input	wire			u0_i_v	,	// u0    input valid

	input  	wire	[A_W+D_W:0] 	u1_i	,	// u1    input payload
	output	wire			u1_i_bp	,	// u1    input backpressured
	input	wire			u1_i_v	,	// u1    input valid

	output 	wire	[A_W+D_W:0] 	l_o	,	// left  input payload
	input	wire			l_o_bp	,	// left  input backpressured
	output	wire			l_o_v	,	// left  input valid

	output 	wire	[A_W+D_W:0] 	r_o	,	// right input payload
	input	wire			r_o_bp	,	// right input backpressured
	output	wire			r_o_v	,	// right input valid

	output 	wire	[A_W+D_W:0] 	u0_o	,	// u0    input payload
	input	wire			u0_o_bp	,	// u0    input backpressured
	output	wire			u0_o_v	,	// u0    input valid

	output 	wire	[A_W+D_W:0] 	u1_o	,	// u1    input payload
	input	wire			u1_o_bp	,	// u1    input backpressured
	output	wire			u1_o_v	,	// u1    input valid
	output 	wire 			done		// done
);
	wire	[2:0] l_sel;	// left select
	wire	[2:0] r_sel;	// right select
	wire	[2:0] u0_sel;	// up0 select
	wire	[2:0] u1_sel;	// up1 select
	
	wire	[A_W+D_W:0] l_o_c;   // left wire
	wire	[A_W+D_W:0] r_o_c;   // left wire
	wire	[A_W+D_W:0] u0_o_c;  // up0 wire
	wire	[A_W+D_W:0] u1_o_c;  // up1 wire

	reg	[A_W+D_W:0] l_o_r;    // left wire
	reg	[A_W+D_W:0] r_o_r;    // left wire
	reg	[A_W+D_W:0] u0_o_r;   // up0 wire
	reg	[A_W+D_W:0] u1_o_r;   // up1 wire

	wire	[A_W-1:0]	l_i_addr;
	wire	[A_W-1:0]	r_i_addr;
	wire	[A_W-1:0]	u0_i_addr;
	wire	[A_W-1:0]	u1_i_addr;
	
	wire	[D_W-1:0]	l_i_d;
	wire	[D_W-1:0]	r_i_d;
	wire	[D_W-1:0]	u0_i_d;
	wire	[D_W-1:0]	u1_i_d;

	wire			l_o_v_c;
	wire			r_o_v_c;
	wire			u0_o_v_c;
	wire			u1_o_v_c;

	assign	l_i_addr	= l_i[A_W+D_W-1:D_W];
	assign	r_i_addr	= r_i[A_W+D_W-1:D_W];
	assign	u0_i_addr	= u0_i[A_W+D_W-1:D_W];
	assign	u1_i_addr	= u1_i[A_W+D_W-1:D_W];

	assign	l_i_d		= l_i[D_W-1:0];
	assign	r_i_d		= r_i[D_W-1:0];
	assign	u0_i_d		= u0_i[D_W-1:0];
	assign	u1_i_d		= u1_i[D_W-1:0];

	pi_route #(.N(N), .A_W(A_W), .D_W(D_W), .posx(posx), .posl(posl)) 
	r(
		.clk		(clk			), 
		.rst		(rst			), 
		.ce		(ce			), 
		.l_i_v		(l_i_v			),
		.l_i_bp		(l_i_bp			),
		.l_i_addr	(l_i_addr		),
		.l_i_data	(l_i_d			),
		.r_i_v		(r_i_v			),
		.r_i_bp		(r_i_bp			),
		.r_i_addr	(r_i_addr		),
	       	.r_i_data	(r_i_d			),
		.u0_i_v		(u0_i_v			),
		.u0_i_bp	(u0_i_bp		),
		.u0_i_addr 	(u0_i_addr		),
		.u0_i_data	(u0_i_d			),
		.u1_i_v		(u1_i_v			),	
		.u1_i_bp	(u1_i_bp		),	
		.u1_i_addr 	(u1_i_addr		),
		.u1_i_data	(u1_i_d			),
		.l_o_v		(l_o_v_c		), 
		.r_o_v		(r_o_v_c		), 
		.u0_o_v		(u0_o_v_c		), 
		.u1_o_v		(u1_o_v_c		),
		.l_o_bp		(l_o_bp			), 
		.r_o_bp		(r_o_bp			), 
		.u0_o_bp	(u0_o_bp		), 
		.u1_o_bp	(u1_o_bp		),
		.l_sel		(l_sel			),
		.r_sel		(r_sel			),
		.u0_sel		(u0_sel			),
		.u1_sel		(u1_sel			)
	);

		Mux3 #(.W(A_W+D_W+1)) l_mux(.s(l_sel[1:0]), .i0(r_i), .i1(u0_i), .i2(u1_i), .o(l_o_c));
		Mux3 #(.W(A_W+D_W+1)) r_mux(.s(r_sel[1:0]), .i0(l_i), .i1(u0_i), .i2(u1_i), .o(r_o_c));

assign	u1_o_c	= r_i;
assign	u0_o_c	= l_i;

reg	l_o_v_r,r_o_v_r,u0_o_v_r,u1_o_v_r;

`ifdef HYPERFLEX
assign	l_o = l_o_c;
assign	r_o = r_o_c;
assign	u0_o = u0_o_c;
assign	u1_o = u1_o_c;
	assign	l_o_v	= l_o_v_c;
	assign	r_o_v	= r_o_v_c;
	assign	u0_o_v	= u0_o_v_c;
	assign	u1_o_v	= u1_o_v_c;
`else	
	always @(posedge clk) begin
		if(rst) begin
			//now	<= 0;
			l_o_r	<= 0;
			r_o_r 	<= 0;
			u0_o_r 	<= 0;
			u1_o_r 	<= 0;
			l_o_v_r	<= 0;
			r_o_v_r	<= 0;
			u0_o_v_r<= 0;
			u1_o_v_r<= 0;
		end else begin
`ifdef DEBUG
			l_o_r 	<= l_sel[2]?{l_o_c}:0;
			r_o_r 	<= r_sel[2]?{r_o_c}:0;
			u0_o_r 	<= u0_sel[2]?{u0_o_c}:0;
			u1_o_r	<= u1_sel[2]?{u1_o_c}:0;

			l_o_v_r	<= l_o_bp ? l_o_v : l_o_v_c;
			r_o_v_r	<= r_o_bp ? r_o_v : r_o_v_c;
			u0_o_v_r<= u0_o_bp ? u0_o_v : u0_o_v_c;
			u1_o_v_r<= u1_o_bp ? u1_o_v : u1_o_v_c;
`endif
`ifndef DEBUG
			if(l_o_bp==1'b0)
			begin
				l_o_r 	<= {l_o_c};
			end
			if(r_o_bp==1'b0)
			begin
			
				r_o_r	<= {r_o_c};
			end
			if(u0_o_bp==1'b0)
			begin
				u0_o_r 	<= {u0_o_c};
			end
			if(u1_o_bp==1'b0)
			begin
				u1_o_r	<= {u1_o_c};
			end
			l_o_v_r	<= l_o_bp ? l_o_v : l_o_v_c;
			r_o_v_r	<= r_o_bp ? r_o_v : r_o_v_c;
			u0_o_v_r<= u0_o_bp ? u0_o_v : u0_o_v_c;
			u1_o_v_r<= u1_o_bp ? u1_o_v : u1_o_v_c;
`endif
		end
	end
		

	assign	l_o_v	= l_o_v_r;
	assign	r_o_v	= r_o_v_r;
	assign	u0_o_v	= u0_o_v_r;
	assign	u1_o_v	= u1_o_v_r;

	assign l_o	= {l_o_r};
	assign r_o	= {r_o_r};
	assign u0_o	= {u0_o_r};
	assign u1_o	= {u1_o_r};
`endif
	`ifdef SIM
	reg done_sig=0;
	always @(posedge clk) begin
		if(~l_i_v & ~r_i_v & ~u0_i_v & ~u1_i_v) begin
			done_sig <= 1;
		end else begin
			done_sig <= 0;
		end
	end
	assign done = done_sig;
	`endif
endmodule

