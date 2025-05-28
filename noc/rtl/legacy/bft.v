`include "commands.h"

module bft #(
	parameter integer WRAP		= 1,
	parameter integer TOPO = 1,
	parameter integer PAT		= 0,
	parameter integer N		= 2,
	parameter integer D_W		= 32,
	parameter integer A_W		= $clog2(N)+1,
	parameter integer LEVELS	= $clog2(N),
	parameter integer LIMIT		= 1024,
	parameter integer RATE		= 100,
	parameter integer SIGMA		= 4,
	parameter integer FD		= 32,
	parameter integer HR            = 1
) (
	input  wire clk,
	input  wire rst,
	input  wire ce,
	input  wire `Cmd cmd,
	input  wire [A_W+D_W+1:0] in,
	output wire [(A_W+D_W+2)*N-1:0] out,
	output wire done_all
);

	reg 	[A_W+D_W:0] 	in_r;
	reg 	[A_W+D_W:0] 	loopback_r 	[N-1:0];

	wire	[A_W+D_W:0]	grid_up		[LEVELS-1:0][2*N-1:0];	
	wire			grid_up_v	[LEVELS-1:0][2*N-1:0];	
	wire 			grid_up_r	[LEVELS-1:0][2*N-1:0];	
	wire 			grid_up_l	[LEVELS-1:0][2*N-1:0];	

	wire 	[A_W+D_W:0] 	grid_dn 	[LEVELS-1:0][2*N-1:0];	
	wire 		 	grid_dn_v 	[LEVELS-1:0][2*N-1:0];	
	wire 	 		grid_dn_r 	[LEVELS-1:0][2*N-1:0];	
	wire 	 		grid_dn_l 	[LEVELS-1:0][2*N-1:0];	

	wire 	[A_W+D_W:0] 	peo 		[N-1:0];	
	wire 		 	peo_v 		[N-1:0];	
	wire 	 		peo_r 		[N-1:0];	
	wire 	 		peo_l 		[N-1:0];	

	wire 	[A_W+D_W:0] 	pei 		[N-1:0];	
	wire 		 	pei_v 		[N-1:0];	
	wire 		 	pei_r 		[N-1:0];	
	wire 		 	pei_l 		[N-1:0];	
	
	// the bizarre configuration of array dimensions and sizes allows
	// verilog reduction operation to be used conveniently
	wire [N-1:0] done_pe;
	wire [N/2-1:0] done_sw [LEVELS-1:0];
	wire [LEVELS-1:0] done_sw_lvl; 
	
  integer now_r=0;
	
	localparam integer TYPE_LEVELS=11;
	localparam TREE_TYPE = {32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0};
	localparam XBAR_TYPE = {32'd1,32'd1,32'd1,32'd1,32'd1,32'd1,32'd1,32'd1,32'd1,32'd1,32'd1};
	localparam MESH0_TYPE = {32'd1,32'd0,32'd1,32'd0,32'd1,32'd0,32'd1,32'd0,32'd1,32'd0,32'd1};
	localparam MESH1_TYPE = {32'd1,32'd1,32'd0,32'd1,32'd1,32'd0,32'd1,32'd1,32'd0,32'd1,32'd1};
	localparam TYPE = (TOPO==`TREE)?TREE_TYPE:(TOPO==`XBAR)?XBAR_TYPE:(TOPO==`MESH0)?MESH0_TYPE:MESH1_TYPE;

	genvar m, n, l, m1, q,hr;
	integer r;
	generate if (WRAP==1) begin: localwrap
		for (q = 0; q < N; q = q + 1) begin : as1
			assign grid_dn[LEVELS-1][q] = in_r;
		end
		always @(posedge clk) begin
			in_r = in;
		end			
	end endgenerate

	reg [(A_W+D_W+2)*N-1:0] out_r;
	genvar x;
	generate for (x = 0; x < N; x = x + 1) begin: routeout
		always @(posedge clk) begin
			out_r[(x+1)*(A_W+D_W+2)-1:x*(A_W+D_W+2)] <= peo[x];
		end
	end endgenerate
	assign out = out_r;	
	
	generate if(N>2) begin: n2
	for (l = 1; l < LEVELS; l = l + 1) begin : ls
		for (m = 0; m < N/(1<<(l+1)); m = m + 1) begin : ms
			for (n = 0; n < (1<<(l)); n = n + 1) begin : ns
				if(((TYPE >> (32*(TYPE_LEVELS-1-l))) & {32{1'b1}})==1) begin: pi_level
					pi_switch_top #(.WRAP(WRAP), .D_W(D_W),.A_W(A_W), .N(N), 
						.posl(l), .posx(m*(1<<l)+n),.FD(FD-2*(HR*(1<<(l>>1)))),.HR(HR*(1<<(l>>1))))
					sb(.clk(clk), .rst(rst), .ce(ce),
						.s_axis_l_wdata(grid_up[l-1][m*(1<<(l+1))+n]),
						.s_axis_l_wvalid(grid_up_v[l-1][m*(1<<(l+1))+n]),
						.s_axis_l_wready(grid_up_r[l-1][m*(1<<(l+1))+n]),
						.s_axis_l_wlast(grid_up_l[l-1][m*(1<<(l+1))+n]),
						.s_axis_r_wdata(grid_up[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.s_axis_r_wvalid(grid_up_v[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.s_axis_r_wready(grid_up_r[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.s_axis_r_wlast(grid_up_l[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.s_axis_u0_wdata(grid_dn[l][m*(1<<(l+1))+n]),
                        .s_axis_u0_wvalid((l == (LEVELS-1)) ? 0 : grid_dn_v[l][m*(1<<(l+1))+n]),
						.s_axis_u0_wready(grid_dn_r[l][m*(1<<(l+1))+n]),
						.s_axis_u0_wlast(grid_dn_l[l][m*(1<<(l+1))+n]),
						.s_axis_u1_wdata(grid_dn[l][m*(1<<(l+1))+n+(1<<(l))]),
                        .s_axis_u1_wvalid((l == (LEVELS-1)) ? 0 : grid_dn_v[l][m*(1<<(l+1))+n+(1<<(l))]),
						.s_axis_u1_wready(grid_dn_r[l][m*(1<<(l+1))+n+(1<<(l))]),
						.s_axis_u1_wlast(grid_dn_l[l][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_l_wdata(grid_dn[l-1][m*(1<<(l+1))+n]),
						.m_axis_l_wvalid(grid_dn_v[l-1][m*(1<<(l+1))+n]),
						.m_axis_l_wready(grid_dn_r[l-1][m*(1<<(l+1))+n]),
						.m_axis_l_wlast(grid_dn_l[l-1][m*(1<<(l+1))+n]),
						.m_axis_r_wdata(grid_dn[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_r_wvalid(grid_dn_v[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_r_wready(grid_dn_r[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_r_wlast(grid_dn_l[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_u0_wdata(grid_up[l][m*(1<<(l+1))+n]),
						.m_axis_u0_wvalid(grid_up_v[l][m*(1<<(l+1))+n]),
						.m_axis_u0_wready(grid_up_r[l][m*(1<<(l+1))+n]),
						.m_axis_u0_wlast(grid_up_l[l][m*(1<<(l+1))+n]),
						.m_axis_u1_wdata(grid_up[l][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_u1_wvalid(grid_up_v[l][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_u1_wready(grid_up_r[l][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_u1_wlast(grid_up_l[l][m*(1<<(l+1))+n+(1<<(l))]),
						.done(done_sw[l][m*(1<<l)+n]));
		    		end
				if(((TYPE >> (32*(TYPE_LEVELS-1-l))) & {32{1'b1}})==0) begin: t_level
					t_switch_top #(.WRAP(WRAP), .D_W(D_W),.A_W(A_W), .N(N), 
						.posl(l), .posx(m*(1<<l)+n),.FD(FD-2*(HR*(1<<(l>>1)))),.HR(HR*(1<<(l>>1))))
					sb(.clk(clk), .rst(rst), .ce(ce),
						.s_axis_l_wdata(grid_up[l-1][m*(1<<(l+1))+n]),
						.s_axis_l_wvalid(grid_up_v[l-1][m*(1<<(l+1))+n]),
						.s_axis_l_wready(grid_up_r[l-1][m*(1<<(l+1))+n]),
						.s_axis_l_wlast(grid_up_l[l-1][m*(1<<(l+1))+n]),
						.s_axis_r_wdata(grid_up[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.s_axis_r_wvalid(grid_up_v[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.s_axis_r_wready(grid_up_r[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.s_axis_r_wlast(grid_up_l[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.s_axis_u0_wdata(grid_dn[l][m*(1<<(l+1))+n]),
                        .s_axis_u0_wvalid((l == (LEVELS-1)) ? 0 : grid_dn_v[l][m*(1<<(l+1))+n]),
						.s_axis_u0_wready(grid_dn_r[l][m*(1<<(l+1))+n]),
						.s_axis_u0_wlast(grid_dn_l[l][m*(1<<(l+1))+n]),
						.m_axis_l_wdata(grid_dn[l-1][m*(1<<(l+1))+n]),
						.m_axis_l_wvalid(grid_dn_v[l-1][m*(1<<(l+1))+n]),
						.m_axis_l_wready(grid_dn_r[l-1][m*(1<<(l+1))+n]),
						.m_axis_l_wlast(grid_dn_l[l-1][m*(1<<(l+1))+n]),
						.m_axis_r_wdata(grid_dn[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_r_wvalid(grid_dn_v[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_r_wready(grid_dn_r[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_r_wlast(grid_dn_l[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.m_axis_u0_wdata(grid_up[l][m*(1<<(l+1))+n]),
						.m_axis_u0_wvalid(grid_up_v[l][m*(1<<(l+1))+n]),
						.m_axis_u0_wready(grid_up_r[l][m*(1<<(l+1))+n]),
						.m_axis_u0_wlast(grid_up_l[l][m*(1<<(l+1))+n]),
						.done(done_sw[l][m*(1<<l)+n]));
		    		end
			end
		end
	end
	end endgenerate
	
	generate for (m = 0; m < N/2; m = m + 1) begin : xs
		client_top #(.D_W(D_W), .A_W(A_W),.N(N), .posx(2*m), .LIMIT(LIMIT), .RATE(RATE), .SIGMA(SIGMA),.WRAP(WRAP), .PAT(PAT))
		cli0(.clk(clk), .rst(rst), .ce(ce), .cmd(cmd),
			.s_axis_c_wdata(pei[2*m]),
			.s_axis_c_wvalid(pei_v[2*m]),
			.s_axis_c_wready(pei_r[2*m]),
			.s_axis_c_wlast(pei_l[2*m]),
			.m_axis_c_wdata(peo[2*m]),
			.m_axis_c_wvalid(peo_v[2*m]),
			.m_axis_c_wready(peo_r[2*m]),
			.m_axis_c_wlast(peo_l[2*m]),
			.done(done_pe[2*m]));
		client_top #(.D_W(D_W), .A_W(A_W),.N(N), .posx(2*m+1), .LIMIT(LIMIT), .SIGMA(SIGMA), .RATE(RATE), .WRAP(WRAP), .PAT(PAT))
		cli1(.clk(clk), .rst(rst), .ce(ce), .cmd(cmd),
			.s_axis_c_wdata(pei[2*m+1]),
			.s_axis_c_wvalid(pei_v[2*m+1]),
			.s_axis_c_wready(pei_r[2*m+1]),
			.s_axis_c_wlast(pei_l[2*m+1]),
			.m_axis_c_wdata(peo[2*m+1]),
			.m_axis_c_wvalid(peo_v[2*m+1]),
			.m_axis_c_wready(peo_r[2*m+1]),
			.m_axis_c_wlast(peo_l[2*m+1]),
			.done(done_pe[2*m+1]));
		if(((TYPE >> (32*(TYPE_LEVELS-1))) & {32{1'b1}})==1) begin: pi_level0
			pi_switch_top #(.WRAP(WRAP), .D_W(D_W),.A_W(A_W), .N(N), .posl(0), .posx(m),.FD(FD-2*HR),.HR(HR))
				sb(.clk(clk), .rst(rst), .ce(ce),
					.s_axis_l_wdata(peo[2*m]),
					.s_axis_l_wvalid(peo_v[2*m]),
					.s_axis_l_wready(peo_r[2*m]),
					.s_axis_l_wlast(peo_l[2*m]),
					.s_axis_r_wdata(peo[2*m+1]),
					.s_axis_r_wvalid(peo_v[2*m+1]),
					.s_axis_r_wready(peo_r[2*m+1]),
					.s_axis_r_wlast(peo_l[2*m+1]),
					.s_axis_u0_wdata(grid_dn[0][2*m]),
					.s_axis_u0_wvalid(grid_dn_v[0][2*m]),
					.s_axis_u0_wready(grid_dn_r[0][2*m]),
					.s_axis_u0_wlast(grid_dn_l[0][2*m]),
					.s_axis_u1_wdata(grid_dn[0][2*m+1]),
					.s_axis_u1_wvalid(grid_dn_v[0][2*m+1]),
					.s_axis_u1_wready(grid_dn_r[0][2*m+1]),
					.s_axis_u1_wlast(grid_dn_l[0][2*m+1]),
					.m_axis_l_wdata(pei[2*m]),
					.m_axis_l_wvalid(pei_v[2*m]),
					.m_axis_l_wready(pei_r[2*m]),
					.m_axis_l_wlast(pei_l[2*m]),
					.m_axis_r_wdata(pei[2*m+1]),
					.m_axis_r_wvalid(pei_v[2*m+1]),
					.m_axis_r_wready(pei_r[2*m+1]),
					.m_axis_r_wlast(pei_l[2*m+1]),
					.m_axis_u0_wdata(grid_up[0][2*m]),
					.m_axis_u0_wvalid(grid_up_v[0][2*m]),
					.m_axis_u0_wready(grid_up_r[0][2*m]),
					.m_axis_u0_wlast(grid_up_l[0][2*m]),
					.m_axis_u1_wdata(grid_up[0][2*m+1]),
					.m_axis_u1_wvalid(grid_up_v[0][2*m+1]),
					.m_axis_u1_wready(grid_up_r[0][2*m+1]),
					.m_axis_u1_wlast(grid_up_l[0][2*m+1]),
					.done(done_sw[0][m]));
		end
		if(((TYPE >> (32*(TYPE_LEVELS-1))) & {32{1'b1}})==0) begin: t_level0
			t_switch_top #(.WRAP(WRAP), .D_W(D_W), .N(N),.A_W(A_W), .posl(0), .posx(m),.FD(FD-2*HR),.HR(HR))
				sb(.clk(clk), .rst(rst), .ce(ce),
					.s_axis_l_wdata(peo[2*m]),
					.s_axis_l_wvalid(peo_v[2*m]),
					.s_axis_l_wready(peo_r[2*m]),
					.s_axis_l_wlast(peo_l[2*m]),
					.s_axis_r_wdata(peo[2*m+1]),
					.s_axis_r_wvalid(peo_v[2*m+1]),
					.s_axis_r_wready(peo_r[2*m+1]),
					.s_axis_r_wlast(peo_l[2*m+1]),
					.s_axis_u0_wdata(grid_dn[0][2*m]),
					.s_axis_u0_wvalid(grid_dn_v[0][2*m]),
					.s_axis_u0_wready(grid_dn_r[0][2*m]),
					.s_axis_u0_wlast(grid_dn_l[0][2*m]),
					.m_axis_l_wdata(pei[2*m]),
					.m_axis_l_wvalid(pei_v[2*m]),
					.m_axis_l_wready(pei_r[2*m]),
					.m_axis_l_wlast(pei_l[2*m]),
					.m_axis_r_wdata(pei[2*m+1]),
					.m_axis_r_wvalid(pei_v[2*m+1]),
					.m_axis_r_wready(pei_r[2*m+1]),
					.m_axis_r_wlast(pei_l[2*m+1]),
					.m_axis_u0_wdata(grid_up[0][2*m]),
					.m_axis_u0_wvalid(grid_up_v[0][2*m]),
					.m_axis_u0_wready(grid_up_r[0][2*m]),
					.m_axis_u0_wlast(grid_up_l[0][2*m]),
					.done(done_sw[0][m]));
		end
	end endgenerate
	
	generate for (l = 0; l < LEVELS; l = l + 1) begin : reduce
		assign done_sw_lvl[l] = &done_sw[l];
	end endgenerate

	assign done_all = &done_pe & &done_sw_lvl & (now_r>16*LIMIT+N); // verilog supports reductions??!

	always@(posedge clk) begin
		now_r     <= now_r + 1;
//		$display("done_pe=%b, done_sw_lvl=%b now=%0d",done_pe,done_sw_lvl,now>16*LIMIT+N);
	end

endmodule
