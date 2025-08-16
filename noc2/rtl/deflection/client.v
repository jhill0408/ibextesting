`include "commands.h"

module client #(
	parameter N 	= 2,		// total number of clients
	parameter D_W	= 32,		// data width
	parameter A_W	= $clog2(N)+1,	// address width
	parameter WRAP  = 1,            // wrapping means throttling of reinjection
	parameter PAT   = `RANDOM,      // default RANDOM pattern
	parameter RATE  = 10,           // rate of injection (in percent) 
	parameter LIMIT = 16,           // when to stop injectin packets
	parameter SIGMA = 4,            // radius for LOCAL traffic
	parameter posx 	= 2		// position
) (
	input  wire clk,		// clock
	input  wire rst,		// reset
	input  wire ce,			// clock enable
	input  wire `Cmd cmd,		// client test command	
	input  wire [A_W+D_W+1:0] o,	// output message from router
	output reg  [A_W+D_W+1:0] i,	// input message from client, registered, validated by i`v
	output wire done		// done
);

`ifdef SYNTHESIS
	reg done_sig;
	reg next_v;
	reg [A_W-2:0] next;
	reg [D_W-1:0] next_d;
	reg [A_W+D_W+1:0] saved0, saved1;  	// save deflected msg for reinject
	integer seed=posx;
	reg [31:0] r;

	always @(posedge clk) begin: inject
		reg [D_W-1:0] tmp;
		if (rst) begin
			i			<= 0;
			r 			<= 0;
		end else begin 
			i			<= 0;
			r 			<= r+1;
			//$display("Time%0d, PE=%0d, r=%0d, RATE=%0d",now, posx, {r}, RATE);
			if(o[A_W+D_W+1] & !o[A_W+D_W]) begin
				$display("Time%0d: Received packet at PE(%0d) with data=%0d",now,posx,o[D_W-1:0]);
			end
			
			if(({r} < RATE)) begin 
				i[A_W+D_W+1]		<= next_v;
				i[A_W+D_W]		<= 0; // does not start deflected...
				i[A_W+D_W-1:D_W]	<= {1'd0,next};
				if(next_v==1) begin
					tmp		= ((posx)*LIMIT+o[D_W-1]); // send packetid instead
					i[D_W-1:0]	<= tmp;
					$display("Time%0d: Sent packet from PE(%0d) to PE(%0d) with packetid=%0d, data=%0d saved0=%0d, saved1=%0d",now,posx,next,((posx)*LIMIT+sent),tmp,saved0[A_W+D_W+1],saved1[A_W+D_W+1]);
				end
			end

		end
	end

	always @(*) begin
		next_v = 0;
		next = 0;
		if (cmd != `Cmd_IDLE) begin				
			next_v = 1;
			next=o;
		end 

	end

	integer now=0;
	always @(posedge clk) begin
		now     <= now + 1;
		if(now==0 && posx==0) begin
			$display("RATE=%0d , N=%0d",RATE,N);
		end
		if(~o[A_W+D_W+1] & ~saved0[A_W+D_W+1] & ~saved1[A_W+D_W+1] & ~i[A_W+D_W+1]) begin
			done_sig <= 1;
		end else begin
			done_sig <= 0;
		end
	end
	
	assign done = done_sig;

`else
	reg done_sig;
	reg next_v;
	reg [A_W-2:0] next;
	reg [D_W-1:0] next_d;
	reg [A_W+D_W+1:0] saved0, saved1;  	// save deflected msg for reinject
	integer seed=posx;
	reg [31:0] r;

	integer attempts=0;
	integer sent=0; // to keep track of worst-case latency

	always @(posedge clk) begin: inject
		reg [D_W-1:0] tmp;
		if (rst) begin
			saved0 			<= 0;
			saved1 			<= 0;
			i			<= 0;
			r 			<= 0;
		end else begin 
			i			<= 0;
			r 			<= {$random}%100; // {} makes it positive
			//$display("Time%0d, PE=%0d, r=%0d, RATE=%0d",now, posx, {r}, RATE);
			if(o[A_W+D_W+1] & (o[A_W+D_W] | o[A_W+D_W-1:D_W]!=posx) & ~saved0[A_W+D_W+1]) begin
				saved0 			<= o;
				$display("Time%0d, PE(%0d), Saved0 with address=%0d, data=%0d",now, posx, o[A_W+D_W-1:D_W],o[D_W-1:0]);
			end else if(o[A_W+D_W+1] & (o[A_W+D_W] | o[A_W+D_W-1:D_W]!=posx) & ~saved1[A_W+D_W+1]) begin
				saved1 			<= o;
				$display("Time%0d, PE(%0d), Saved1 with address=%0d, data=%0d",now, posx, o[A_W+D_W-1:D_W],o[D_W-1:0]);
			end else if(o[A_W+D_W+1] & (o[A_W+D_W] | o[A_W+D_W-1:D_W]!=posx) & saved0[A_W+D_W+1] & saved1[A_W+D_W+1]) begin
				$display("Time%0d: Error Condition, trying to save two packets in PE(%0d)",now,posx);
				$finish;
			end else if(o[A_W+D_W+1] & !o[A_W+D_W]) begin
				$display("Time%0d: Received packet at PE(%0d) with data=%0d",now,posx,o[D_W-1:0]);
			end
			
			if(saved0[A_W+D_W+1] & ({r} < 50 | !WRAP)) begin
				saved0 			<= 0;
				i[A_W+D_W+1]		<= 1;
				i[A_W+D_W]		<= 0; // does not start deflected...
				i[A_W+D_W-1:D_W]	<= saved0[A_W+D_W-1:D_W];
				i[D_W-1:0]		<= saved0[D_W-1:0];
				$display("Time%0d, PE=%0d, Reattempt0 with address=%0d, data=%0d",now, posx, saved0[A_W+D_W-1:D_W],saved0[D_W-1:0]);
			end else if(saved1[A_W+D_W+1] & ({r} < 50 | !WRAP)) begin
				saved1 			<= 0;
				i[A_W+D_W+1]		<= 1;
				i[A_W+D_W]		<= 0; // does not start deflected...
				i[A_W+D_W-1:D_W]	<= saved1[A_W+D_W-1:D_W];
				i[D_W-1:0]		<= saved1[D_W-1:0];
				$display("Time%0d, PE=%0d, Reattempt1 with address=%0d, data=%0d",now, posx, saved1[A_W+D_W-1:D_W],saved1[D_W-1:0]);
			end else if(~saved0[A_W+D_W+1] & ~saved1[A_W+D_W+1] &
				~(o[A_W+D_W+1] & (o[A_W+D_W] | o[A_W+D_W-1:D_W]!=posx) & ~saved0[A_W+D_W+1]) &
				((attempts<LIMIT & {r} < RATE) | attempts > sent | cmd!=`Cmd_RND)) begin 
				i[A_W+D_W+1]		<= next_v;
				i[A_W+D_W]		<= 0; // does not start deflected...
				i[A_W+D_W-1:D_W]	<= {1'd0,next};
				if(next_v==1) begin
					sent		<= sent + 1;
					//tmp		= $random(seed);
					tmp		= ((posx)*LIMIT+sent); // send packetid instead
					i[D_W-1:0]	<= tmp;
					$display("Time%0d: Sent packet from PE(%0d) to PE(%0d) with packetid=%0d, data=%0d saved0=%0d, saved1=%0d",now,posx,next,((posx)*LIMIT+sent),tmp,saved0[A_W+D_W+1],saved1[A_W+D_W+1]);
				end
			end

			// separately attempting injection
			if((attempts<LIMIT & {r} < RATE) | cmd!=`Cmd_RND) begin 
				attempts		<= attempts + 1;
				$display("Time%0d: Attempted packetid=%0d at PE(%0d) with saved0=%0d saved1=%0d attempts=%0d sent=%0d",now,(posx*LIMIT+attempts),posx, saved0[A_W+D_W+1],saved1[A_W+D_W+1],attempts, sent);
			end
		end
	end

	always @(*) begin
		next_v = 0;
		next = 0;
		if (cmd != `Cmd_IDLE) begin				
			next_v = 1;

			case (cmd)
				default: ;
				`Cmd_01: if (posx==0) next=2'd01; else begin next_v=0; end
				`Cmd_02: if (posx==0) next=2'd10; else begin next_v=0; end
				`Cmd_03: if (posx==0) next=2'd11; else begin next_v=0; end
				`Cmd_10: if (posx==1) next=2'd00; else begin next_v=0; end
				`Cmd_12: if (posx==1) next=2'd10; else begin next_v=0; end
				`Cmd_13: if (posx==1) next=2'd11; else begin next_v=0; end
				`Cmd_20: if (posx==2) next=2'd00; else begin next_v=0; end
				`Cmd_21: if (posx==2) next=2'd01; else begin next_v=0; end
				`Cmd_23: if (posx==2) next=2'd11; else begin next_v=0; end
				`Cmd_30: if (posx==3) next=2'd00; else begin next_v=0; end
				`Cmd_31: if (posx==3) next=2'd01; else begin next_v=0; end
				`Cmd_32: if (posx==3) next=2'd10; else begin next_v=0; end
				`Cmd_02_12: if (posx==0) next=2'd10; else if (posx==1) next=2'd10; else begin next_v=0; end
				`Cmd_01_12: if (posx==0) next=2'd01; else if (posx==1) next=2'd10; else begin next_v=0; end
				`Cmd_40_70: if (posx==4) next=2'd00; else if (posx==7) next=2'd00; else begin next_v=0; end
				`Cmd_02_25: if (posx==0) next=2'd10; else if (posx==2) next=3'd101; else begin next_v=0; end
				`Cmd_swap: if (posx==0) next=2'd01; else if (posx==1) next=2'd00; else begin next_v=0; end
				// randomized testing
				`Cmd_RND: 
					case (PAT)
						`RANDOM: begin 
							next=get_safe_rnd({$random}%N); 
						end
						`LOCAL: begin 
							next=get_safe_rnd(local_window(local_rnd(posx),N)); 
						end
						`BITREV: begin 
							next=bitrev(posx) % N; 
						end
						`TORNADO: begin 
							next=tornado(posx, N); 
						end
					endcase
			endcase
		end 

	end

	integer now=0;
	always @(posedge clk) begin
		now     <= now + 1;
		if(now==0 && posx==0) begin
			$display("RATE=%0d , N=%0d",RATE,N);
		end
		if(attempts==sent & attempts==LIMIT & ~o[A_W+D_W+1] & ~saved0[A_W+D_W+1] & ~saved1[A_W+D_W+1] & ~i[A_W+D_W+1]) begin
//			$display("Time%0d, PE=%0d, attempts=%d, sent=%d\n",now,posx,attempts,sent);
			done_sig <= 1;
		end else begin
			done_sig <= 0;
		end
	end
	
	assign done = done_sig;

`endif

	// avoid self-packets for now
	function integer get_safe_rnd(input integer tmp);
		get_safe_rnd=(tmp==posx)?((tmp+1)%N):tmp%N;
	endfunction

	function integer local_rnd(input integer i);
		local_rnd = i + {$random} % SIGMA - SIGMA/2;
	endfunction

	// avoiding SystemVerilog for
	// iverilog compatibility
	function integer local_window(input integer r, input integer max);
		local_window = (r < 0)? 0 : (r >= max) ? (max-1) : r;
	endfunction

	function [9:0] bitrev(input [9:0] i);
		bitrev = {i[0],i[1],i[2],i[3],i[4],i[5],i[6],i[7],i[8],i[9]};
	endfunction

	function integer tornado(input integer i, input integer max);
		tornado = (i + max/2-1) % max;
	endfunction


endmodule

