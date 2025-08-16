`include "commands.h"
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */
/* verilator lint_off UNUSEDPARAM */
/* verilator lint_off UNUSEDSIGNAL */
/* verilator lint_off UNUSEDGENVAR */

module bft #(
	parameter WRAP		= 1,
	parameter PAT		= 0,
	parameter N		= 2,
	parameter D_W		= 32,
	parameter A_W		= $clog2(N)+1,
	parameter LEVELS	= $clog2(N),
	parameter LIMIT		= 1024,
	parameter RATE		= 100
) (
	input  wire clk,
	input  wire rst,
	input  wire ce,
	//input  wire `Cmd cmd,
	input  wire [A_W+D_W+1:0] in,
	output wire [(A_W+D_W+2)*N-1:0] out,
	output wire done_all,
	input wire [A_W+D_W+1:0] peo [N-1:0],
	output wire [A_W+D_W+1:0] pei [N-1:0],
	input wire [N-1:0] done_pe
);

	reg [A_W+D_W+1:0] in_r;
	reg [A_W+D_W+1:0] loopback_r [N-1:0];
	wire [A_W+D_W+1:0] grid_up [LEVELS-1:0][2*N-1:0];	
	wire [A_W+D_W+1:0] grid_dn [LEVELS-1:0][2*N-1:0];	

	
	// the bizarre configuration of array dimensions and sizes allows
	// verilog reduction operation to be used conveniently
	wire [N/2-1:0] done_sw [LEVELS-1:0];
	wire [LEVELS-1:0] done_sw_lvl; 
	
	localparam integer TYPE_LEVELS=11;
	// tree 
`ifdef TREE
	localparam TYPE = {32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0,32'd0};
`endif
/*
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
*/

	genvar m, n, l, m1, q;
	integer r;
	generate if (WRAP==1) begin: localwrap
		for (q = 0; q < N; q = q + 1) begin : as1
			assign grid_dn[LEVELS-1][q] = in_r;
		end
		always @(posedge clk) begin
			in_r <= in;
		end			
	end endgenerate
	
	generate if (WRAP==0) begin: defl
		always @(posedge clk) begin
			for (r = 0; r < N; r = r + 1) begin : as2
				loopback_r[r] <= grid_up[LEVELS-1][r];
			end
		end
		for (q = 0; q < N; q = q + 1) begin : as3
			assign grid_dn[LEVELS-1][q] = loopback_r[q];
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
					pi_switch #(.WRAP(WRAP), .D_W(D_W), .N(N), 
						.posl(l), .posx(m*(1<<l)+n), .A_W(A_W))
					sb(.clk(clk), .rst(rst), .ce(ce),
						.l_i(grid_up[l-1][m*(1<<(l+1))+n]),
						.r_i(grid_up[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.u0_i(grid_dn[l][m*(1<<(l+1))+n]),
						.u1_i(grid_dn[l][m*(1<<(l+1))+n+(1<<(l))]),
						.l_o(grid_dn[l-1][m*(1<<(l+1))+n]),
						.r_o(grid_dn[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.u0_o(grid_up[l][m*(1<<(l+1))+n]),
						.u1_o(grid_up[l][m*(1<<(l+1))+n+(1<<(l))]),
						.done(done_sw[l][m*(1<<l)+n]));
		    		end
				if(((TYPE >> (32*(TYPE_LEVELS-1-l))) & {32{1'b1}})==0) begin: t_level
					t_switch #(.WRAP(WRAP), .D_W(D_W), .N(N), 
						.posl(l), .posx(m*(1<<l)+n), .A_W(A_W))
					sb(.clk(clk), .rst(rst), .ce(ce),
						.l_i(grid_up[l-1][m*(1<<(l+1))+n]),
						.r_i(grid_up[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.u0_i(grid_dn[l][m*(1<<(l+1))+n]),
						.l_o(grid_dn[l-1][m*(1<<(l+1))+n]),
						.r_o(grid_dn[l-1][m*(1<<(l+1))+n+(1<<(l))]),
						.u0_o(grid_up[l][m*(1<<(l+1))+n]),
						.done(done_sw[l][m*(1<<l)+n]));
		    		end
			end
		end
	end
	end endgenerate
	
	generate for (m = 0; m < N/2; m = m + 1) begin : xs
	/*
		client #(.D_W(D_W), .N(N), .posx(2*m), .LIMIT(LIMIT), .RATE(RATE), .WRAP(WRAP), .PAT(PAT))
		cli0(.clk(clk), .rst(rst), .ce(ce), .cmd(cmd),
			.i(peo[2*m]),
			.o(pei[2*m]),
			.done(done_pe[2*m]));
		client #(.D_W(D_W), .N(N), .posx(2*m+1), .LIMIT(LIMIT), .RATE(RATE), .WRAP(WRAP), .PAT(PAT))
		cli1(.clk(clk), .rst(rst), .ce(ce), .cmd(cmd),
			.i(peo[2*m+1]),
			.o(pei[2*m+1]),
			.done(done_pe[2*m+1]));
			*/

		if(((TYPE >> (32*(TYPE_LEVELS-1))) & {32{1'b1}})==1) begin: pi_level0
			pi_switch #(.WRAP(WRAP), .D_W(D_W), .N(N), .posl(0), .posx(m), .A_W(A_W))
				sb(.clk(clk), .rst(rst), .ce(ce),
					.l_i(peo[2*m]),
					.r_i(peo[2*m+1]),
					.u0_i(grid_dn[0][2*m]),
					.u1_i(grid_dn[0][2*m+1]),
					.l_o(pei[2*m]),
					.r_o(pei[2*m+1]),
					.u0_o(grid_up[0][2*m]),
					.u1_o(grid_up[0][2*m+1]),
					.done(done_sw[0][m]));
		end
		if(((TYPE >> (32*(TYPE_LEVELS-1))) & {32{1'b1}})==0) begin: t_level0
			t_switch #(.WRAP(WRAP), .D_W(D_W), .N(N), .posl(0), .posx(m), .A_W(A_W))
				sb(.clk(clk), .rst(rst), .ce(ce),
					.l_i(peo[2*m]),
					.r_i(peo[2*m+1]),
					.u0_i(grid_dn[0][2*m]),
					.l_o(pei[2*m]),
					.r_o(pei[2*m+1]),
					.u0_o(grid_up[0][2*m]),
					.done(done_sw[0][m]));
		end
	end endgenerate
	
	generate for (l = 0; l < LEVELS; l = l + 1) begin : reduce
		assign done_sw_lvl[l] = &done_sw[l];
	end endgenerate

	assign done_all = &done_pe & &done_sw_lvl & (now>16*LIMIT+N); // verilog supports reductions??!

	integer now=0;
	always@(posedge clk) begin
		now     <= now + 1;
	end

endmodule
