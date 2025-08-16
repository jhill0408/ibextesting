module example #(
	parameter N		= 16
) (
	input wire clk,
	input  wire [N-1:0] in,
	output reg [N-1:0] out
);

	localparam BOOLARR = {32'd1,32'd1,32'd1,32'd1,32'd0,32'd0,32'd0,32'd0};

	genvar l;
	for (l = 1; l < N; l = l + 1) begin : loopl
		always @(posedge clk) begin
			$display("inside l=%d",l);
		end
		// What I want to do --> if(BOOLARR[l]==1) begin: crazy1
		// What I have to do \|/
		if(((BOOLARR >> (32*l)) & {32{1'b1}})==1) begin: crazy1
			always @(posedge clk) begin
				$display("inferred l=%d",l);
				out[l] <= in[l];
			end
		end
		if(((BOOLARR >> (32*l)) & {32{1'b1}})==0) begin: crazy1
			always @(posedge clk) begin
				$display("not inferred l=%d",l);
				out[l] <= ~in[l];
			end
		end
	end
	
endmodule
