/* verilator lint_off UNUSEDSIGNAL */
module t_switch #(
	parameter N	= 4,		// number of clients
	parameter WRAP	= 0,		// crossbar?
	parameter A_W	= $clog2(N)+1,	// addr width
	parameter D_W	= 32,		// data width
	parameter posl  = 0,		// which level
	parameter posx 	= 0		// which position
) (
	input  wire clk,		// clock
	input  wire rst,		// reset
	input  wire ce,			// clock enable
	input  wire [A_W+D_W+1:0] l_i,	// left input
	input  wire [A_W+D_W+1:0] r_i,	// right input
	input  wire [A_W+D_W+1:0] u0_i,	// up0 input
	output wire [A_W+D_W+1:0] l_o,	// left output
	output wire [A_W+D_W+1:0] r_o,	// right output
	output wire [A_W+D_W+1:0] u0_o,	// up0 output
        output wire done                // done
);
	
	wire l_i_v;			// left valid
	wire r_i_v;			// right valid
	wire u0_i_v;			// up0 valid
	wire l_i_defl;			// left deflect
	wire r_i_defl;			// right deflect
	wire u0_i_defl;			// up0 deflect
	wire [A_W-1:0] l_i_addr;	// left address
	wire [A_W-1:0] r_i_addr;	// right address
	wire [A_W-1:0] u0_i_addr;	// up0 address
	wire [D_W-1:0] l_i_d;		// left data
	wire [D_W-1:0] r_i_d;		// right data
	wire [D_W-1:0] u0_i_d;		// up0 data

	wire l_o_v;			// left valid
	wire r_o_v;			// right valid
	wire u0_o_v;			// up0 valid
	wire l_o_defl;			// left deflected
	wire r_o_defl;			// right deflected
	wire u0_o_defl;			// up0 deflected
	wire [A_W-1:0] l_o_addr;	// left address
	wire [A_W-1:0] r_o_addr;	// right address
	wire [A_W-1:0] u0_o_addr;	// up0 address
	wire [D_W-1:0] l_o_d;		// left data
	wire [D_W-1:0] r_o_d;		// right data
	wire [D_W-1:0] u0_o_d;		// up0 data
	
	wire [2:0] l_sel;		// left select
	wire [2:0] r_sel;		// right select
	wire [2:0] u0_sel;		// up0 select
	
	wire [A_W+D_W-1:0] l_o_c;	// left wire
	wire [A_W+D_W-1:0] r_o_c;	// left wire
	wire [A_W+D_W-1:0] u0_o_c;	// up0 wire

	reg [A_W+D_W+1:0] l_o_r;	// left wire
	reg [A_W+D_W+1:0] r_o_r;	// left wire
	reg [A_W+D_W+1:0] u0_o_r;   	// up0 wire

	assign l_i_v = l_i[A_W+D_W+1];
	assign r_i_v = r_i[A_W+D_W+1];
	assign u0_i_v = u0_i[A_W+D_W+1];
	assign l_i_defl = l_i[A_W+D_W];
	assign r_i_defl = r_i[A_W+D_W];
	assign u0_i_defl = u0_i[A_W+D_W];
	assign l_i_addr = l_i[A_W+D_W-1:D_W];
	assign r_i_addr = r_i[A_W+D_W-1:D_W];
	assign u0_i_addr = u0_i[A_W+D_W-1:D_W];
	assign l_i_d = l_i[D_W-1:0];
	assign r_i_d = r_i[D_W-1:0];
	assign u0_i_d = u0_i[D_W-1:0];

	generate if (WRAP) begin : full
		t_route #(.N(N), .A_W(A_W), .posx(posx), .posl(posl)) 
		r(.clk(clk), .rst(rst), .ce(ce), 
		.l_i_v(l_i_v),
		.l_i_defl(l_i_defl),
		.l_i_addr(l_i_addr),
		.l_o_v(l_o_v),
		.l_o_defl(l_o_defl),
		.l_sel(l_sel),
		.r_i_v(r_i_v),
		.r_i_defl(r_i_defl),
		.r_i_addr(r_i_addr),
		.r_o_v(r_o_v),
		.r_o_defl(r_o_defl),
		.r_sel(r_sel),
		.u0_i_v(u0_i_v),
		.u0_i_defl(u0_i_defl),
		.u0_i_addr(u0_i_addr),
		.u0_o_v(u0_o_v),
		.u0_o_defl(u0_o_defl),
		.u0_sel(u0_sel));

		Mux3 #(.W(A_W+D_W)) l_mux(.s(l_sel[1:0]), .i0(l_i[A_W+D_W-1:0]), .i1(r_i[A_W+D_W-1:0]), .i2(u0_i[A_W+D_W-1:0]), .o(l_o_c));
		Mux3 #(.W(A_W+D_W)) r_mux(.s(r_sel[1:0]), .i0(l_i[A_W+D_W-1:0]), .i1(r_i[A_W+D_W-1:0]), .i2(u0_i[A_W+D_W-1:0]), .o(r_o_c));
		Mux3 #(.W(A_W+D_W)) u0_mux(.s(u0_sel[1:0]), .i0(l_i[A_W+D_W-1:0]), .i1(r_i[A_W+D_W-1:0]), .i2(u0_i[A_W+D_W-1:0]), .o(u0_o_c));
	end endgenerate

	generate if (!WRAP) begin : partial
		t_route_lean #(.N(N), .A_W(A_W), .posx(posx), .posl(posl)) 
		r(.clk(clk), .rst(rst), .ce(ce), 
		.l_i_v(l_i_v),
		.l_i_defl(l_i_defl),
		.l_i_addr(l_i_addr),
		.l_o_v(l_o_v),
		.l_o_defl(l_o_defl),
		.l_sel(l_sel),
		.r_i_v(r_i_v),
		.r_i_defl(r_i_defl),
		.r_i_addr(r_i_addr),
		.r_o_v(r_o_v),
		.r_o_defl(r_o_defl),
		.r_sel(r_sel),
		.u0_i_v(u0_i_v),
		.u0_i_defl(u0_i_defl),
		.u0_i_addr(u0_i_addr),
		.u0_o_v(u0_o_v),
		.u0_o_defl(u0_o_defl),
		.u0_sel(u0_sel));

		Mux2 #(.W(A_W+D_W)) l_mux(.s(l_sel[1]), .i0(r_i[A_W+D_W-1:0]), .i1(u0_i[A_W+D_W-1:0]), .o(l_o_c));
		Mux2 #(.W(A_W+D_W)) r_mux(.s(r_sel[1]), .i0(l_i[A_W+D_W-1:0]), .i1(u0_i[A_W+D_W-1:0]), .o(r_o_c));
		Mux2 #(.W(A_W+D_W)) u0_mux(.s(u0_sel[0]), .i0(l_i[A_W+D_W-1:0]), .i1(r_i[A_W+D_W-1:0]), .o(u0_o_c));
	end endgenerate


	always @(posedge clk) begin
		if(rst) begin
			l_o_r <= 0;
			r_o_r <= 0;
			u0_o_r <= 0;
		end else begin
`ifdef DEBUG
			l_o_r <= l_sel[2]?{l_o_v,l_o_defl,l_o_c}:0;
			r_o_r <= r_sel[2]?{r_o_v,r_o_defl,r_o_c}:0;
			u0_o_r <= u0_sel[2]?{u0_o_v,u0_o_defl,u0_o_c}:0;
`endif
			l_o_r <= {l_o_v,l_o_defl,l_o_c};
			r_o_r <= {r_o_v,r_o_defl,r_o_c};
			u0_o_r <= {u0_o_v,u0_o_defl,u0_o_c};
		end
	end
			
	assign l_o = {l_o_r};
	assign r_o = {r_o_r};
	assign u0_o = {u0_o_r};

	assign l_o_addr = l_o_c[A_W+D_W-1:D_W];
	assign r_o_addr = r_o_c[A_W+D_W-1:D_W];
	assign u0_o_addr = u0_o_c[A_W+D_W-1:D_W];
	
	assign l_o_d = l_o_c[D_W-1:0];
	assign r_o_d = r_o_c[D_W-1:0];
	assign u0_o_d = u0_o_c[D_W-1:0];

	`ifdef DEBUG
		always @(posedge clk) begin
			if(l_i_v) begin
				$display("Time%0d, At Level=%0d, TSwitch=%0d, detected packet %0d[%0d] at Left input with destination=%0d",now, posl, posx, l_i_defl, l_i_d, l_i_addr);
			end
			if(l_o_v) begin
				$display("Time%0d, At Level=%0d, TSwitch=%0d, sending packet %0d to Left output with destination=%0d",now, posl, posx, l_o_d, l_o_addr);
			end
			if(l_o_defl) begin
				$display("Time%0d, At Level=%0d, TSwitch=%0d, deflection packet %0d to Left output with destination=%0d",now, posl, posx, l_o_d, l_o_addr);
			end
			if(r_i_v) begin
				$display("Time%0d, At Level=%0d, TSwitch=%0d, detected packet %0d[%0d] at Right input with destination=%0d",now, posl, posx, r_i_defl, r_i_d, r_i_addr);
			end
			if(r_o_v) begin
				$display("Time%0d, At Level=%0d, TSwitch=%0d, sending packet %0d to Right output with destination=%0d",now, posl, posx, r_o_d, r_o_addr);
			end
			if(r_o_defl) begin
				$display("Time%0d, At Level=%0d, TSwitch=%0d, deflection packet %0d to Right output with destination=%0d",now, posl, posx, r_o_d, r_o_addr);
			end
			if(u0_i_v) begin
				$display("Time%0d, At Level=%0d, TSwitch=%0d, detected packet %0d[%0d] at Up0 input with destination=%0d",now, posl, posx, u0_i_defl, u0_i_d, u0_i_addr);
			end
			if(u0_o_v) begin
				$display("Time%0d, At Level=%0d, TSwitch=%0d, sending packet %0d to Up0 output with destination=%0d",now, posl, posx, u0_o_d, u0_o_addr);
			end
			if(u0_o_defl) begin
				$display("Time%0d, At Level=%0d, TSwitch=%0d, deflection packet %0d to Up0 output with destination=%0d",now, posl, posx, u0_o_d, u0_o_addr);
			end
		end
	`endif


	integer now=0;
	reg done_sig=0;
	always @(posedge clk) begin
		now     <= now + 1;
		if(~l_i_v & ~r_i_v & ~u0_i_v) begin
			done_sig <= 1;
		end else begin
			done_sig <= 0;
		end
	end

        assign done = done_sig;

endmodule

