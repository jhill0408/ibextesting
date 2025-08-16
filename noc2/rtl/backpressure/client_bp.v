`include	"commands.h"

module client 
#(
	parameter N 	= 2,		// total number of clients
	parameter D_W	= 32,		// data width
	parameter A_W	= $clog2(N)+1,	// address width
	parameter WRAP  = 1,            // wrapping means throttling of reinjection
	parameter PAT   = `RANDOM,      // default RANDOM pattern
	parameter RATE  = 10,           // rate of injection (in percent) 
	parameter LIMIT = 16,           // when to stop injectin packets
	parameter SIGMA = 4,            // radius for LOCAL traffic
	parameter posx 	= 2,		// position
	parameter filename = "posx"
)
(
	input				clk,
	input				rst,
	input				ce,
	input		`Cmd		cmd,
	
	input		[A_W+D_W:0]	c_i,
	input				c_i_v,
	output	wire			c_i_bp,

	output	reg	[A_W+D_W:0]	c_o,
	output	reg			c_o_v,
	input				c_o_bp,

	output	wire			done
);

assign	c_i_bp	= 1'b0;

`ifdef SYNTHETIC

integer	r, attempts,sent;
reg 			done_sig;
reg	[A_W-1:0]	next;
reg			next_v;
reg 	[D_W-1:0] 	tmp;

always@(posedge clk)
begin
	if (rst==1'b1)
	begin
		c_o		<= 'b0;
		c_o_v		<= 1'b0;
		r		<= 'b0;
		attempts	<= 0;
		sent		<= 0;
	end
	else
	begin
		r	<= {$random}%100;
		if (c_o_bp==1'b0)
		begin
			if(((attempts<LIMIT & {r} < RATE) | attempts > sent | cmd!=`Cmd_RND)) 
			begin
				c_o_v			<= 1'b1;
				c_o[A_W+D_W-1:D_W]	<= next;
				if(next_v==1) 
				begin
					sent		<= sent + 1;
					tmp		= ((posx)*LIMIT+sent); // send packetid instead
					c_o[D_W-1:0]	<= tmp;
					$display("Time%0d: Sent packet from PE(%0d) to PE(%0d) with packetid=%0d , data=%0d ",now,posx,next,((posx)*LIMIT+sent),tmp);
				end
			end
			else
			begin
				c_o_v	<= 1'b0;
			end
		end
		else
		begin
		//	c_o_v	<= 1'b0;
		end
	
		if ((attempts<LIMIT & {r} < RATE) | cmd!=`Cmd_RND)
		begin
			attempts	<= attempts + 1;
			$display("Time%0d: Attempted packetid=%0d at PE(%0d) attempts=%0d sent=%0d",now,(posx*LIMIT+attempts),posx, attempts, sent);

		end
		
		if(c_i_v==1'b1) 
		begin
			$display("Time%0d: Received packet at PE(%0d) with data=%0d packetid=%0d ",now-1,posx,c_i[D_W-1:0],c_i[D_W-1:0]);
		end
	end
end

always @(*) 
begin
	next_v = 0;
	next = 0;
	if (cmd != `Cmd_IDLE) 
	begin				
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
		if(attempts==sent & attempts==LIMIT & ~c_i_v) begin
//			$display("Time%0d, PE=%0d, attempts=%d, sent=%d\n",now,posx,attempts,sent);
			done_sig <= 1;
		end else begin
			done_sig <= 0;
		end
	end
	
	assign done = done_sig;


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

`elsif REAL

integer		r, attempts,sent;
reg		done_sig;
reg	[31:0]	next	[0:99999999];
reg			next_v;
reg 	[D_W-1:0] 	tmp;
initial
begin
	`ifdef SIM_AXIIC
		//$readmemh(filename,next);
$readmemh("autogen_0.trace",next);
	`endif
	`ifndef SIM_AXIIC
		$readmemh($sformatf("autogen_%0d.trace",posx),next);
	`endif
end

always@(posedge clk)
begin
	if (rst==1'b1)
	begin
		c_o		<= 'b0;
		c_o_v		<= 1'b0;
		r		<= 'b0;
		attempts	<= 0;
		sent		<= 0;
	end
	else
	begin
		r	<= {$random}%100;
		if (c_o_bp==1'b0)
		begin
			if(((next[sent][11:8]!=4'hf & {r} < RATE) | attempts > sent | cmd!=`Cmd_RND)) 
			begin
				if(next[sent][A_W-1:0]!=posx)
				begin
					c_o_v			<= 1'b1;
					c_o[A_W+D_W-1:D_W]	<= next[sent][A_W-1:0];
					sent		<= sent + 1;
					tmp		= ((posx)*1485078+sent); // send packetid instead
					c_o[D_W-1:0]	<= tmp;
					$display("Time%0d: Sent packet from PE(%0d) to PE(%0d) with packetid=%0d , data=%0d ",now,posx,next[sent][A_W-1:0],((posx)*1485078+sent),tmp);
				end
				else
				begin
					sent	<= sent + 1;
					c_o_v	<= 1'b0;
					$display("Time%0d: Sent packet from PE(%0d) to PE(%0d) with packetid=%0d , data=%0d ",now,posx,next[sent][A_W-1:0],((posx)*1485078+sent),((posx)*1485078+sent));
			$display("Time%0d: Received packet at PE(%0d) with data=%0d packetid=%0d ",now,posx,((posx)*1485078+sent),((posx)*1485078+sent));
				end
			end
			else
			begin
				c_o_v	<= 1'b0;
			end
		end
		else
		begin
			//c_o_v	<= 1'b0;
		end
	
		if ((next[attempts][11:8]!=4'hf & {r} < RATE) | cmd!=`Cmd_RND)
		begin
			attempts	<= attempts + 1;
			$display("Time%0d: Attempted packetid=%0d at PE(%0d) attempts=%0d sent=%0d",now,(posx*1485078+attempts),posx, attempts, sent);

		end
		
		if(c_i_v==1'b1) 
		begin
			$display("Time%0d: Received packet at PE(%0d) with data=%0d packetid=%0d ",now-1,posx,c_i[D_W-1:0],c_i[D_W-1:0]);
		end
	end
end

	integer now=0;
	always @(posedge clk) begin
		now     <= now + 1;
		if(now==0 && posx==0) begin
			$display("RATE=%0d , N=%0d",RATE,N);
		end
		if(attempts==sent & next[sent][11:8]==4'hf & ~c_i_v) begin
//			$display("Time%0d, PE=%0d, attempts=%d, sent=%d\n",now,posx,attempts,sent);
			done_sig <= 1;
		end else begin
			done_sig <= 0;
		end
	end

assign done = done_sig;
`endif
endmodule

