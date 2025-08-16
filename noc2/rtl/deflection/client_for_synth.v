`include "commands.h"

module client #(
	parameter N 	= 2,		// total number of clients
	parameter D_W	= 32,		// data width
	parameter A_W	= $clog2(N)+1,	// address width
	parameter WRAP  = 1,            // wrapping means throttling of reinjection
	parameter RATE  = 10,           // rate of injection (in percent) 
	parameter PAT   = `LOCAL,       // ignored -- here for compatibility
	parameter LIMIT = 16,           // when to stop injectin packets
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

	reg [A_W-1:0] loc=posx;
	reg done_sig;
	always @(posedge clk) begin
		loc <= { loc[A_W-1:0], loc[A_W-1] ^ loc[0] };
		loc <= loc+1;
	end

	reg [D_W-1:0] cntr;
	always @(posedge clk) begin
		if (rst) begin
			i	<= 0;
			cntr <= 0;
		end else begin 
			if(o[A_W+D_W+1]) begin
				cntr            <= o[D_W-1:0] + o[A_W+D_W:D_W];
			end else begin
				cntr           <= cntr+1;
			end 
			if ( !o[A_W+D_W+1]) begin 
				i[A_W+D_W+1]	<= 1'b1;
				i[A_W+D_W]		<= 1'b0;
				i[A_W+D_W-1:D_W]<= loc;
				i[D_W-1:0]      <= cntr;
			end
		end
	end

	assign done = 0;
endmodule
