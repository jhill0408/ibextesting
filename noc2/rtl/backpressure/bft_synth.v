`include "commands.h"

module bft #(
	parameter WRAP		= 1,
	parameter N		= 4,
parameter D_W=32,
	parameter A_W		= $clog2(N)+1,
	parameter LEVELS	= $clog2(N),
	parameter FD		= 32,
parameter HR=1
) (
	input  wire clk,
	input  wire rst,
	input  wire ce,

	input	wire	[((A_W+D_W+1)*N)-1:0]	peo_p,
	input	wire	[N-1:0]			peo_v_p,
	input	wire	[N-1:0]			peo_l_p,
	output	reg	[N-1:0]			peo_r_p,

	output	reg	[((A_W+D_W+1)*N)-1:0]	pei_p,
	output	reg	[N-1:0]			pei_v_p,
	output	reg	[N-1:0]			pei_l_p,
	input	wire	[N-1:0]			pei_r_p

);

	wire	[A_W+D_W-1:0]	grid_up		[LEVELS-1:0][2*N-1:0];	
	wire			grid_up_v	[LEVELS-1:0][2*N-1:0];	
	wire 			grid_up_r	[LEVELS-1:0][2*N-1:0];	
	wire 			grid_up_l	[LEVELS-1:0][2*N-1:0];	

	wire 	[A_W+D_W-1:0] 	grid_dn 	[LEVELS-1:0][2*N-1:0];	
	wire 		 	grid_dn_v 	[LEVELS-1:0][2*N-1:0];	
	wire 	 		grid_dn_r 	[LEVELS-1:0][2*N-1:0];	
	wire 	 		grid_dn_l 	[LEVELS-1:0][2*N-1:0];	

	reg 	[A_W+D_W-1:0] 	peo 		[N-1:0];	
	reg 	[N-1:0]	 	peo_v 		;	
	wire 	[N-1:0]		peo_r 		;	
	reg 	[N-1:0]		peo_l 		;	

	wire 	[A_W+D_W-1:0] 	pei 		[N-1:0];	
	wire 	[N-1:0]	 	pei_v 		;	
	reg 	[N-1:0]	 	pei_r 		;	
	wire 	[N-1:0]	 	pei_l 		;	

	
	localparam integer TYPE_LEVELS=11;
	// tree 
`ifdef TREE
	localparam TYPE = {32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0};
`endif
	// xbar 
`ifdef XBAR
	localparam TYPE = {32'd1,32'd1,32'd1,32'd1,32'd1,32'd1,32'd1,32'd1,32'd1,32'd1,32'd1};
`endif
	// mesh0 0.5 
`ifdef MESH0
	localparam TYPE = {32'd1,32'd0,32'd1,32'd0,32'd1,32'd0,32'd1,32'd0,32'd1,32'd0,32'd1};
`endif
	// mesh0 0.67 
`ifdef MESH1
	localparam TYPE = {32'd1,32'd1,32'd0,32'd1,32'd1,32'd0,32'd1,32'd1,32'd0,32'd1,32'd1};
`endif

	genvar m, n, l, m1;
	integer r;

	genvar x;
	generate for (x = 0; x < N; x = x + 1) begin: routeout
		always @(posedge clk) 
		begin
			peo[x]	<= peo_p[(x+1)*(A_W+D_W+1)-1:x*(A_W+D_W+1)];
			pei_p[(x+1)*(A_W+D_W+1)-1:x*(A_W+D_W+1)]	<= pei[x]; 
		end
	end endgenerate

	always@(posedge clk)
	begin
		peo_v	<= peo_v_p;
		peo_l	<= peo_l_p;
		peo_r_p	<= peo_r;

		pei_v_p	<= pei_v;
		pei_l_p	<= pei_l;
		pei_r	<= pei_r_p;
	end
	
	generate if(N>2) begin: n2
	for (l = 1; l < LEVELS; l = l + 1) begin : ls
		for (m = 0; m < N/(1<<(l+1)); m = m + 1) begin : ms
			for (n = 0; n < (1<<(l)); n = n + 1) begin : ns
				if(((TYPE >> (32*(TYPE_LEVELS-1-l))) & {32{1'b1}})==1) begin: pi_level
					pi_switch_top #(.WRAP(WRAP), .D_W(D_W),.A_W(A_W), .N(N), 
						.posl(l), .posx(m*(1<<l)+n),.FD(FD-2*(HR*(1<<(l>>1)))),.HR(HR*(1<<(l>>1))))
					sb(.clk(clk), .rst(rst ), .ce(ce),
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
						.m_axis_u1_wlast(grid_up_l[l][m*(1<<(l+1))+n+(1<<(l))])
						);
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
						.m_axis_u0_wlast(grid_up_l[l][m*(1<<(l+1))+n])
						);
		    		end
			end
		end
	end
	end endgenerate
	
	generate for (m = 0; m < N/2; m = m + 1) begin : xs
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
					.m_axis_u1_wlast(grid_up_l[0][2*m+1])
					);
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
					.m_axis_u0_wlast(grid_up_l[0][2*m])
					);
		end
	end endgenerate
endmodule
