`include "commands.h"

module bft_tb #(
	parameter WRAP		= 1,
	parameter LIMIT		= 512,
	parameter RATE		= 100,
	parameter PAT		= `RANDOM,
	parameter N		= 512, 
	parameter D_W		= 32,
	parameter A_W		= $clog2(N)+1);

	// synthesis translate_off
	reg clk;
	reg [1:0] rst;
	reg [5:0] cmd;

	wire [(A_W+D_W+2)*N-1:0] out;
	reg  [A_W+D_W+1:0] in;

	initial begin
		clk = 0;
		rst = 2'b11;
		cmd = `Cmd_IDLE;
	end
	
	integer addr;

	bft #(.D_W(D_W), .N(N), .WRAP(WRAP), .LIMIT(LIMIT), .RATE(RATE), .PAT(PAT))
		p(.clk(clk), .rst(rst[0]), .ce(1'b1), .cmd(cmd), 
			.out(out), .in(in), .done_all(done_all));
	
	always begin
		clk = ~clk;	
		#0.5;
	end

	always @(posedge clk) begin
		rst = rst >> 1;
		in = 0;

`ifdef UNIT_TEST_RND
		cmd = `Cmd_RND;
`endif
`ifdef UNIT_TEST_TRIANGLE_T
		case ($time)
		default: cmd = `Cmd_IDLE;
		10:cmd = `Cmd_30;
		14:cmd = `Cmd_01_12;
		150: begin
			$display("Done received from all clients at time=%0d",now);
			$finish;
		end
		endcase
`endif
`ifdef UNIT_TEST_TRIANGLE_PI
		case ($time)
		default: cmd = `Cmd_IDLE;
		10:cmd = `Cmd_40_70;
		16:cmd = `Cmd_02_25;
		150: begin
			$display("Done received from all clients at time=%0d",now);
			$finish;
		end
		endcase
`endif
`ifdef UNIT_TEST_UP0_DEFLECT
		case ($time)
		default: cmd = `Cmd_IDLE;
		10:cmd = `Cmd_30;
		14:cmd = `Cmd_swap;
		150: begin
			$display("Done received from all clients at time=%0d",now);
			$finish;
		end
		endcase
`endif
`ifdef UNIT_TEST_SW0_DEFLECT
		case ($time)
		default: cmd = `Cmd_IDLE;
		10:cmd = `Cmd_02_12;
		12:cmd = `Cmd_12;
		150: begin
			$display("Done received from all clients at time=%0d",now);
			$finish;
		end
		endcase
`endif
`ifdef UNIT_TEST_REACHABILITY2
		case ($time)
		default: cmd = `Cmd_IDLE;
		10:cmd = `Cmd_01;
		20:cmd = `Cmd_10;
		30:cmd = `Cmd_01;
		40:cmd = `Cmd_10;
		150: begin
			$display("Done received from all clients at time=%0d",now);
			$finish;
		end
		endcase
`endif
`ifdef UNIT_TEST_REACHABILITY4
		case ($time)
		default: cmd = `Cmd_IDLE;
		10:cmd = `Cmd_01;
		20:cmd = `Cmd_02;
		30:cmd = `Cmd_03;
		40:cmd = `Cmd_10;
		50:cmd = `Cmd_12;
		60:cmd = `Cmd_13;
		70:cmd = `Cmd_20;
		80:cmd = `Cmd_21;
		90:cmd = `Cmd_23;
		100:cmd = `Cmd_30;
		110:cmd = `Cmd_31;
		120:cmd = `Cmd_32;
		150: begin
			$display("Done received from all clients at time=%0d",now);
			$finish;
		end
		endcase
`endif
		
`ifdef UNIT_TEST_RND
		if(done_all) begin
			$display("Done received from all clients at time=%0d",now);
			$finish;
		end
`endif

	end
	
	integer now=0;
	always @(posedge clk) begin
		if(rst) begin
			now <= 0;
		end else begin
			now <= now + 1;
		end
	end


`ifdef DUMP
	initial
	begin
		$dumpfile("bft.vcd");
		$dumpvars(0,bft_tb);
	end
`endif

endmodule
