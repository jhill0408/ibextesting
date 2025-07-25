// i think there is a bug where if the final piece of data for MPRF or MEM, and idle is high, it send 2 packets instead of 1
module descriptor #(
) (
    input  logic                clk,
    input  logic                rst_n,     // active-low synchronous reset
    input  logic                start,     // example control in
    input  logic [4:0]          start_addr,
    input  logic [32-1:0]   in_data,
    output logic out_valid,
    output logic [9:0] out_addr,
    input logic in_valid,
    input logic descriptor_allowed,
    output logic [4:0]          mprf_addr,
    output logic                mprf_rd_en,

    output logic [32-1:0]   out_data,
    output logic read_mem_o,
    output logic [31:0] mem_addr_o,
    input logic mem_rvalid,
    input logic mem_gnt,
    input logic [31:0] mem_data_i,
    output logic idle

);

logic [9:0] output_addr;
logic [31:0] out_data_r;
logic out_valid_r;
logic ready_done;
logic [4:0] descriptor_mprf_addr_r;
/* verilator lint_off UNUSEDSIGNAL */
logic [4:0] data_mprf_addr_r;
/* verilator lint_on UNUSEDSIGNAL */
logic mprf_rd_en_r;
logic startmin1;
logic do_mprf_data_addr;
/* verilator lint_off UNUSEDSIGNAL */
logic do_mprf_data_addr_min1;
logic descriptor_allowed_min1;
logic mprf_rd_en_min1;
/* verilator lint_on UNUSEDSIGNAL */
logic input_not_descriptor;
logic [31:0] mem_addr;
logic read_mem;
logic mem_mode;
logic mem_was_granted;
logic is_length;
logic [4:0] length_cntr;

assign mem_addr_o = mem_addr;
assign read_mem_o = read_mem;

assign out_valid = out_valid_r & descriptor_allowed; // pretty sure my outvalid logic is wrong btw
assign out_addr = output_addr;
//assign mprf_addr =(start && startmin1) ? start_addr + 1 : descriptor_mprf_addr_r; // I think this would be useful if I make that fix to descriptor_allowed, also would have to do same thing to rd_en
//assign mprf_addr = ((in_data[31:29] == 3'b001 && !input_not_descriptor) || input_not_descriptor) ? in_data[4:0] : descriptor_mprf_addr_r;
assign mprf_addr = (input_not_descriptor ||is_length) ? data_mprf_addr_r : descriptor_mprf_addr_r;
assign mprf_rd_en = mprf_rd_en_r;
assign out_data = out_data_r;
  
always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        idle <= 'b1;
        ready_done <= 'b0;
        output_addr <= 'b0;
        out_valid_r <= 'b0;
        out_data_r <= 'b0;
        descriptor_mprf_addr_r <= 'b0;
        mprf_rd_en_r <= 'b0;
        startmin1 <= 'b0;
        data_mprf_addr_r <= 'b0;
        do_mprf_data_addr <= 'b0;
        do_mprf_data_addr_min1 <= 'b0;
        descriptor_allowed_min1 <= 'b0;
        mprf_rd_en_min1 <= 'b0;
        input_not_descriptor <= 'b0;
        mem_addr <= 'b0;
        read_mem <= 'b0;
        mem_mode <= 'b0;
        mem_was_granted <= 'b0;
        is_length <= 'b0;
        length_cntr <= 'b0;
    end else begin
        startmin1 <= start;
        do_mprf_data_addr_min1 <= do_mprf_data_addr;
        descriptor_allowed_min1 <= descriptor_allowed;
        mprf_rd_en_min1 <= mprf_rd_en;

        if (mem_gnt) begin
            mem_was_granted <= 'b1;
        end
        
        if (start && startmin1) begin
            idle <= 'b0;
            output_addr <= in_data[9:0];
            descriptor_mprf_addr_r <= start_addr + 1; // prolly a cycle too late?
            mprf_rd_en_r <= 'b1;
        end
        if (mprf_rd_en && descriptor_allowed && !(!input_not_descriptor && in_data[31:29] == 3'b001)) begin
            if (!(input_not_descriptor)) begin
            descriptor_mprf_addr_r <= descriptor_mprf_addr_r + 1;
            end
        end
        if (out_valid) begin
            output_addr <= output_addr + 1;
        end
        if (input_not_descriptor) begin
            if (!mem_mode) begin
                if (length_cntr == 5'b0) begin
                    input_not_descriptor <= 'b0;

                    
                end else begin
                    length_cntr <= length_cntr - 1;
                    data_mprf_addr_r <= data_mprf_addr_r + 1;
                end




            out_data_r <= in_data;
            out_valid_r <= 1'b1;
            //input_not_descriptor <= 1'b0;
            end else begin
                read_mem <= length_cntr > 0;
                if (mem_rvalid & mem_was_granted) begin // i think i dont need this mem_Was_granted signal
                if (length_cntr == 5'b1) begin
                    mprf_rd_en_r <= 1'b1;
                end
                if (length_cntr == 5'b0) begin
                    input_not_descriptor <= 'b0;
                    read_mem <= 'b0;
                    //descriptor_mprf_addr_r <= descriptor_mprf_addr_r + 1; //?? maybe comment out
                    mprf_rd_en_r <= 1'b1;
                    mem_mode <= 1'b0;
                end else begin
                    length_cntr <= length_cntr - 1;
                    mem_addr <= mem_addr + 4;

                end
                    out_data_r <= mem_data_i;
                    out_valid_r <= 1'b1;
                    //input_not_descriptor <= 1'b0;
                    //read_mem <= 1'b0;
                    //descriptor_mprf_addr_r <= descriptor_mprf_addr_r + 1;
                    //mprf_rd_en_r <= 1'b1;
                    //mem_mode <= 1'b0;
                end

            end
        end
        if (!idle) begin
            if (in_valid && !ready_done && !input_not_descriptor) begin // can probably do a lot of this work combinationally if it doesnt affect max freq
                unique case (in_data[31:29]) // only should change out_data_r when descriptor allowed, technically dont need descriptor allowed for first message but not worth to have it not needed for that

                    3'b000: begin
                        if (descriptor_allowed) begin
                            if (!is_length) begin
                            if (in_data == 32'b0) begin
                                out_data_r <= 'b1;
                                out_valid_r <= 'b1;
                                output_addr <= {output_addr[9:5], 5'b11111};
                                ready_done <= 'b1;
                                mprf_rd_en_r <= 'b0;
                            end else begin
                            out_data_r <= in_data;
                            out_valid_r <= 1'b1;
                            descriptor_mprf_addr_r <= descriptor_mprf_addr_r + 1;
                            mprf_rd_en_r <= 'b1;
                            end
                            end else begin
                                length_cntr <= in_data[4:0];
                                if (!mem_mode) begin
                                input_not_descriptor <= 'b1;
                                //do_mprf_data_addr <= 'b1;
                                is_length <= 'b0;
                                
                                data_mprf_addr_r <= data_mprf_addr_r + 1;
                                end else begin
                                    input_not_descriptor <= 'b1;
                                    is_length <= 'b0;
                                    mem_addr <= mem_addr + 4;
                                end

                            end
                        end
                        end
                    3'b001: begin // RN/data at single addr in mprf
                        if (descriptor_allowed) begin
                            data_mprf_addr_r <= in_data[4:0];
                            //do_mprf_data_addr <= 'b1;
                            do_mprf_data_addr <= 'b1;
                            out_valid_r <= 'b0;
                            //input_not_descriptor <= 'b1;
                            is_length <= 'b1;
                            


                            

                            /*
                            if (do_mprf_data_addr_min1 & descriptor_allowed_min1 & mprf_rd_en_min1) begin
                                out_valid_r <= 'b1;
                                out_data_r <= in_data;
                                do_mprf_data_addr <= 'b0;
                                //descriptor_mprf_addr_r <= descriptor_mprf_addr_r + 1; // prolly a cycle too late?

                            end */


                        end
                        end
                    3'b010: begin
                        if (descriptor_allowed) begin // experiment with diff fetch lengths and whatnot maybe
                            out_valid_r <= 'b0;
                            //input_not_descriptor <= 'b1;
                            mem_addr <= {3'b0, in_data[28:0]};
                            read_mem <= 1'b1;
                            mprf_rd_en_r <= 'b0;
                            mem_mode <= 'b1;
                            is_length <= 'b1;
                        end
                        end
                    3'b011: begin
                        end
                    3'b100: begin
                        end
                    3'b101: begin
                        end
                    3'b110: begin
                        end
                    3'b111: begin
                        end
                    default: begin
                    end
                endcase

            end
        end
        if (ready_done & descriptor_allowed) begin
            idle <= 'b1;
            ready_done <= 'b0;
            out_valid_r <= 'b0; // assign out_valid = out_valid_r & descriptor_allowed;
            out_data_r <= 'b0;
        end
    end
end













endmodule
