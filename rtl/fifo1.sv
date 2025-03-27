// FILE MODIFIED FROM ECE327 FIFO CODE!
module fifo1
#(
    parameter integer D_W = 32,
    parameter integer DEPTH = 8
)
(
    input  logic clk,
    input  logic rst,
    input  logic write,
    input  logic read,
    input  logic signed [D_W-1:0] data_in,
    output logic signed [D_W-1:0] data_out,
    output wire                  full,
    output wire                  empty,
    output logic [$clog2(DEPTH)-1:0] occup
);

reg [$clog2(DEPTH)-1:0] rdaddr;
reg [$clog2(DEPTH)-1:0] wraddr;
//reg [$clog2(DEPTH)-1:0] occup;
reg [DEPTH-1:0] [D_W-1:0]           mem ;
/* verilator lint_off WIDTHEXPAND */
assign full = occup == (DEPTH-1) ? 1 : 0;

assign empty = occup == 0 ? 1 : 0;
//assign occup_o = occup;

always @(posedge clk or negedge rst) begin
    if (!rst) begin
        mem<=0;
    end else begin
    data_out <= read? mem[rdaddr] : '0;
    if (write)
        mem[wraddr] <= data_in;
    end
end

always @(posedge clk or negedge rst) begin
    if (!rst) begin
        rdaddr <= 0;
        wraddr <= 0;
        occup  <= 0;
    end else begin
        if (write & !read) begin
            wraddr <= (wraddr == DEPTH-1)? 0 :wraddr + 1;
        end else if (read & !write) begin
            rdaddr <= (rdaddr == DEPTH-1)? 0 : rdaddr + 1;
        end else if (write & read) begin
            wraddr <= (wraddr == DEPTH-1)? 0 :wraddr + 1;
            rdaddr <= (rdaddr == DEPTH-1)? 0 : rdaddr + 1;
            /* verilator lint_on WIDTHEXPAND */
        end
        if (read && !write) begin
            occup <= occup - 1;
        end
        else if (!read && write) begin
            occup <= occup + 1;
        end
    end
end

endmodule

