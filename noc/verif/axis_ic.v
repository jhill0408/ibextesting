module axis_ic#
(
parameter N=16,
	parameter	D_W =32,
	parameter	A_W = 8,
parameter PAT=0,
	parameter	WRAP = 1,
	parameter	RATE = 100,
	parameter	LIMIT = 1024,
	parameter	SIGMA = 3
)
(
    (*dont_touch="true"*)input  [N-1:0]     m_valid,
    (*dont_touch="true"*)output  [N-1:0]      m_ready,
    (*dont_touch="true"*)input   [N-1:0 ]     m_last,

    `ifndef SIM_AXIIC
    (*dont_touch="true"*)input clk,
    (*dont_touch="true"*)input rst,
    `endif
        
    `ifdef Nis2
    (*dont_touch="true"*)input    [31:0]        m_data_0,
    (*dont_touch="true"*)input    [31:0]        m_data_1,
    (*dont_touch="true"*)output    [31:0]       s_data_0,
    (*dont_touch="true"*)output    [31:0]       s_data_1,
    (*dont_touch="true"*)input     [3:0]        m_dest_0,
    (*dont_touch="true"*)input     [3:0]        m_dest_1,
    (*dont_touch="true"*)output[3:0]            s_dest_0,
    (*dont_touch="true"*)output[3:0]            s_dest_1 ,   
    `endif
    `ifdef Nis4
     (*dont_touch="true"*)input    [31:0]        m_data_0,
    (*dont_touch="true"*)input    [31:0]        m_data_1,
    (*dont_touch="true"*)input    [31:0]        m_data_2,
    (*dont_touch="true"*)input    [31:0]        m_data_3,
    (*dont_touch="true"*)output    [31:0]       s_data_0,
    (*dont_touch="true"*)output    [31:0]       s_data_1,
    (*dont_touch="true"*)output    [31:0]       s_data_2,
    (*dont_touch="true"*)output    [31:0]       s_data_3,
    (*dont_touch="true"*)input     [3:0]        m_dest_0,
    (*dont_touch="true"*)input     [3:0]        m_dest_1,
    (*dont_touch="true"*)input     [3:0]        m_dest_2,
    (*dont_touch="true"*)input     [3:0]        m_dest_3,
    (*dont_touch="true"*)output[3:0]            s_dest_0,
    (*dont_touch="true"*)output[3:0]            s_dest_1,
    (*dont_touch="true"*)output[3:0]            s_dest_2,
    (*dont_touch="true"*)output[3:0]            s_dest_3,
    `endif
    `ifdef Nis8
    (*dont_touch="true"*)input    [31:0]        m_data_0,
    (*dont_touch="true"*)input    [31:0]        m_data_1,
    (*dont_touch="true"*)input    [31:0]        m_data_2,
    (*dont_touch="true"*)input    [31:0]        m_data_3,
    (*dont_touch="true"*)input    [31:0]        m_data_4,
    (*dont_touch="true"*)input    [31:0]        m_data_5,
    (*dont_touch="true"*)input    [31:0]        m_data_6,
    (*dont_touch="true"*)input    [31:0]        m_data_7,
        
    (*dont_touch="true"*)output    [31:0]       s_data_0,
    (*dont_touch="true"*)output    [31:0]       s_data_1,
    (*dont_touch="true"*)output    [31:0]       s_data_2,
    (*dont_touch="true"*)output    [31:0]       s_data_3,
    (*dont_touch="true"*)output    [31:0]       s_data_4,
    (*dont_touch="true"*)output    [31:0]       s_data_5,
    (*dont_touch="true"*)output    [31:0]       s_data_6,
    (*dont_touch="true"*)output    [31:0]       s_data_7,
        
    (*dont_touch="true"*)input     [3:0]        m_dest_0,
    (*dont_touch="true"*)input     [3:0]        m_dest_1,
    (*dont_touch="true"*)input     [3:0]        m_dest_2,
    (*dont_touch="true"*)input     [3:0]        m_dest_3,
    (*dont_touch="true"*)input     [3:0]        m_dest_4,
    (*dont_touch="true"*)input     [3:0]        m_dest_5,
    (*dont_touch="true"*)input     [3:0]        m_dest_6,
    (*dont_touch="true"*)input     [3:0]        m_dest_7,
        
    (*dont_touch="true"*)output[3:0]            s_dest_0,
    (*dont_touch="true"*)output[3:0]            s_dest_1,
    (*dont_touch="true"*)output[3:0]            s_dest_2,
    (*dont_touch="true"*)output[3:0]            s_dest_3,
    (*dont_touch="true"*)output[3:0]            s_dest_4,
    (*dont_touch="true"*)output[3:0]            s_dest_5,
    (*dont_touch="true"*)output[3:0]            s_dest_6,
    (*dont_touch="true"*)output[3:0]            s_dest_7,
    `endif
     `ifdef Nis16
    (*dont_touch="true"*)input    [31:0]        m_data_0,
    (*dont_touch="true"*)input    [31:0]        m_data_1,
    (*dont_touch="true"*)input    [31:0]        m_data_2,
    (*dont_touch="true"*)input    [31:0]        m_data_3,
    (*dont_touch="true"*)input    [31:0]        m_data_4,
    (*dont_touch="true"*)input    [31:0]        m_data_5,
    (*dont_touch="true"*)input    [31:0]        m_data_6,
    (*dont_touch="true"*)input    [31:0]        m_data_7,
    (*dont_touch="true"*)input    [31:0]        m_data_8,
    (*dont_touch="true"*)input    [31:0]        m_data_9,
    (*dont_touch="true"*)input    [31:0]        m_data_10,
    (*dont_touch="true"*)input    [31:0]        m_data_11,
    (*dont_touch="true"*)input    [31:0]        m_data_12,
    (*dont_touch="true"*)input    [31:0]        m_data_13,
    (*dont_touch="true"*)input    [31:0]        m_data_14,
    (*dont_touch="true"*)input    [31:0]        m_data_15,

        
    (*dont_touch="true"*)output    [31:0]       s_data_0,
    (*dont_touch="true"*)output    [31:0]       s_data_1,
    (*dont_touch="true"*)output    [31:0]       s_data_2,
    (*dont_touch="true"*)output    [31:0]       s_data_3,
    (*dont_touch="true"*)output    [31:0]       s_data_4,
    (*dont_touch="true"*)output    [31:0]       s_data_5,
    (*dont_touch="true"*)output    [31:0]       s_data_6,
    (*dont_touch="true"*)output    [31:0]       s_data_7,
    (*dont_touch="true"*)output    [31:0]       s_data_8,
    (*dont_touch="true"*)output    [31:0]       s_data_9,
    (*dont_touch="true"*)output    [31:0]       s_data_10,
    (*dont_touch="true"*)output    [31:0]       s_data_11,
    (*dont_touch="true"*)output    [31:0]       s_data_12,
    (*dont_touch="true"*)output    [31:0]       s_data_13,
    (*dont_touch="true"*)output    [31:0]       s_data_14,
    (*dont_touch="true"*)output    [31:0]       s_data_15,

        
    (*dont_touch="true"*)input     [3:0]        m_dest_0,
    (*dont_touch="true"*)input     [3:0]        m_dest_1,
    (*dont_touch="true"*)input     [3:0]        m_dest_2,
    (*dont_touch="true"*)input     [3:0]        m_dest_3,
    (*dont_touch="true"*)input     [3:0]        m_dest_4,
    (*dont_touch="true"*)input     [3:0]        m_dest_5,
    (*dont_touch="true"*)input     [3:0]        m_dest_6,
    (*dont_touch="true"*)input     [3:0]        m_dest_7,
    (*dont_touch="true"*)input     [3:0]        m_dest_8,
    (*dont_touch="true"*)input     [3:0]        m_dest_9,
    (*dont_touch="true"*)input     [3:0]        m_dest_10,
    (*dont_touch="true"*)input     [3:0]        m_dest_11,
    (*dont_touch="true"*)input     [3:0]        m_dest_12,
    (*dont_touch="true"*)input     [3:0]        m_dest_13,
    (*dont_touch="true"*)input     [3:0]        m_dest_14,
    (*dont_touch="true"*)input     [3:0]        m_dest_15,
        
    (*dont_touch="true"*)output[3:0]            s_dest_0,
    (*dont_touch="true"*)output[3:0]            s_dest_1,
    (*dont_touch="true"*)output[3:0]            s_dest_2,
    (*dont_touch="true"*)output[3:0]            s_dest_3,
    (*dont_touch="true"*)output[3:0]            s_dest_4,
    (*dont_touch="true"*)output[3:0]            s_dest_5,
    (*dont_touch="true"*)output[3:0]            s_dest_6,
    (*dont_touch="true"*)output[3:0]            s_dest_7,
    (*dont_touch="true"*)output[3:0]            s_dest_8,
    (*dont_touch="true"*)output[3:0]            s_dest_9,
    (*dont_touch="true"*)output[3:0]            s_dest_10,
    (*dont_touch="true"*)output[3:0]            s_dest_11,
    (*dont_touch="true"*)output[3:0]            s_dest_12,
    (*dont_touch="true"*)output[3:0]            s_dest_13,
    (*dont_touch="true"*)output[3:0]            s_dest_14,
    (*dont_touch="true"*)output[3:0]            s_dest_15,
    
    `endif
    (*dont_touch="true"*)output	[N-1:0]		s_valid,
    (*dont_touch="true"*)input	[N-1:0]		s_ready,
    (*dont_touch="true"*)output	[N-1:0]		s_last

);
`ifdef  SIM_AXIIC
reg	clk;
reg	rst;
wire	[N-1:0]	done;

initial
begin
	clk	<= 0;
	rst	<= 1;
	#10;
	clk	<= 1;
	rst	<= 1;
	#10;
	rst	<= 0;
	forever
	begin
		clk	<= ~clk;
		#10;
		if(&(done)==1'b1)
        begin
                    #1000;
                    $finish;
        end
	end

end

`ifdef Nis2
	client_top_0
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(0	)
	)
	inst_0(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[0]	),
		.s_axis_c_wvalid	(s_valid[0]	),
		.s_axis_c_wready	(s_ready[0]	),
		.s_axis_c_wlast		(s_last[0]	),
		.s_axis_c_tdest		(s_dest[0]	),
		.m_axis_c_wdata		(m_data[0]	),
		.m_axis_c_wvalid	(m_valid[0]	),
		.m_axis_c_wready	(m_ready[0]	),
		.m_axis_c_wlast		(m_last[0]	),
		.m_axis_c_tdest		(m_dest[0]	),
		.done			(done[0])	          
	
	);
	client_top_1
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(1	)
	)
	inst_1(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[1]	),
		.s_axis_c_wvalid	(s_valid[1]	),
		.s_axis_c_wready	(s_ready[1]	),
		.s_axis_c_wlast		(s_last[1]	),
		.s_axis_c_tdest		(s_dest[1]	),
		.m_axis_c_wdata		(m_data[1]	),
		.m_axis_c_wvalid	(m_valid[1]	),
		.m_axis_c_wready	(m_ready[1]	),
		.m_axis_c_wlast		(m_last[1]	),
		.m_axis_c_tdest		(m_dest[1]	),
		.done			(done[1])	          
	
	);
`endif
`ifdef Nis4
	client_top_0
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(0	)
	)
	inst_0(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[0]	),
		.s_axis_c_wvalid	(s_valid[0]	),
		.s_axis_c_wready	(s_ready[0]	),
		.s_axis_c_wlast		(s_last[0]	),
		.s_axis_c_tdest		(s_dest[0]	),
		.m_axis_c_wdata		(m_data[0]	),
		.m_axis_c_wvalid	(m_valid[0]	),
		.m_axis_c_wready	(m_ready[0]	),
		.m_axis_c_wlast		(m_last[0]	),
		.m_axis_c_tdest		(m_dest[0]	),
		.done			(done[0])	          
	);
	client_top_1
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(1	)
	)
	inst_1(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[1]	),
		.s_axis_c_wvalid	(s_valid[1]	),
		.s_axis_c_wready	(s_ready[1]	),
		.s_axis_c_wlast		(s_last[1]	),
		.s_axis_c_tdest		(s_dest[1]	),
		.m_axis_c_wdata		(m_data[1]	),
		.m_axis_c_wvalid	(m_valid[1]	),
		.m_axis_c_wready	(m_ready[1]	),
		.m_axis_c_wlast		(m_last[1]	),
		.m_axis_c_tdest		(m_dest[1]	),
		.done			(done[1])	          
	);
	client_top_2
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(2	)
	)
	inst_2(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[2]	),
		.s_axis_c_wvalid	(s_valid[2]	),
		.s_axis_c_wready	(s_ready[2]	),
		.s_axis_c_wlast		(s_last[2]	),
		.s_axis_c_tdest		(s_dest[2]	),
		.m_axis_c_wdata		(m_data[2]	),
		.m_axis_c_wvalid	(m_valid[2]	),
		.m_axis_c_wready	(m_ready[2]	),
		.m_axis_c_wlast		(m_last[2]	),
		.m_axis_c_tdest		(m_dest[2]	),
		.done			(done[2])	          
	);
	client_top_3
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(3	)
	)
	inst_3(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[3]	),
		.s_axis_c_wvalid	(s_valid[3]	),
		.s_axis_c_wready	(s_ready[3]	),
		.s_axis_c_wlast		(s_last[3]	),
		.s_axis_c_tdest		(s_dest[3]	),
		.m_axis_c_wdata		(m_data[3]	),
		.m_axis_c_wvalid	(m_valid[3]	),
		.m_axis_c_wready	(m_ready[3]	),
		.m_axis_c_wlast		(m_last[3]	),
		.m_axis_c_tdest		(m_dest[3]	),
		.done			(done[3])	          
	);
`endif
`ifdef Nis8
	client_top_0
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(0	)
	)
	inst_0(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[0]	),
		.s_axis_c_wvalid	(s_valid[0]	),
		.s_axis_c_wready	(s_ready[0]	),
		.s_axis_c_wlast		(s_last[0]	),
		.s_axis_c_tdest		(s_dest[0]	),
		.m_axis_c_wdata		(m_data[0]	),
		.m_axis_c_wvalid	(m_valid[0]	),
		.m_axis_c_wready	(m_ready[0]	),
		.m_axis_c_wlast		(m_last[0]	),
		.m_axis_c_tdest		(m_dest[0]	),
		.done			(done[0])	          
	);
	client_top_1
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(1	)
	)
	inst_1(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[1]	),
		.s_axis_c_wvalid	(s_valid[1]	),
		.s_axis_c_wready	(s_ready[1]	),
		.s_axis_c_wlast		(s_last[1]	),
		.s_axis_c_tdest		(s_dest[1]	),
		.m_axis_c_wdata		(m_data[1]	),
		.m_axis_c_wvalid	(m_valid[1]	),
		.m_axis_c_wready	(m_ready[1]	),
		.m_axis_c_wlast		(m_last[1]	),
		.m_axis_c_tdest		(m_dest[1]	),
		.done			(done[1])	          
	);
	client_top_2
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(2	)
	)
	inst_2(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[2]	),
		.s_axis_c_wvalid	(s_valid[2]	),
		.s_axis_c_wready	(s_ready[2]	),
		.s_axis_c_wlast		(s_last[2]	),
		.s_axis_c_tdest		(s_dest[2]	),
		.m_axis_c_wdata		(m_data[2]	),
		.m_axis_c_wvalid	(m_valid[2]	),
		.m_axis_c_wready	(m_ready[2]	),
		.m_axis_c_wlast		(m_last[2]	),
		.m_axis_c_tdest		(m_dest[2]	),
		.done			(done[2])	          
	);
	client_top_3
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(3	)
	)
	inst_3(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[3]	),
		.s_axis_c_wvalid	(s_valid[3]	),
		.s_axis_c_wready	(s_ready[3]	),
		.s_axis_c_wlast		(s_last[3]	),
		.s_axis_c_tdest		(s_dest[3]	),
		.m_axis_c_wdata		(m_data[3]	),
		.m_axis_c_wvalid	(m_valid[3]	),
		.m_axis_c_wready	(m_ready[3]	),
		.m_axis_c_wlast		(m_last[3]	),
		.m_axis_c_tdest		(m_dest[3]	),
		.done			(done[3])	          
	);
	client_top_4
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(4	)
	)
	inst_4(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[4]	),
		.s_axis_c_wvalid	(s_valid[4]	),
		.s_axis_c_wready	(s_ready[4]	),
		.s_axis_c_wlast		(s_last[4]	),
		.s_axis_c_tdest		(s_dest[4]	),
		.m_axis_c_wdata		(m_data[4]	),
		.m_axis_c_wvalid	(m_valid[4]	),
		.m_axis_c_wready	(m_ready[4]	),
		.m_axis_c_wlast		(m_last[4]	),
		.m_axis_c_tdest		(m_dest[4]	),
		.done			(done[4])	          
	);
	client_top_5
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(5	)
	)
	inst_5(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[5]	),
		.s_axis_c_wvalid	(s_valid[5]	),
		.s_axis_c_wready	(s_ready[5]	),
		.s_axis_c_wlast		(s_last[5]	),
		.s_axis_c_tdest		(s_dest[5]	),
		.m_axis_c_wdata		(m_data[5]	),
		.m_axis_c_wvalid	(m_valid[5]	),
		.m_axis_c_wready	(m_ready[5]	),
		.m_axis_c_wlast		(m_last[5]	),
		.m_axis_c_tdest		(m_dest[5]	),
		.done			(done[5])	          
	);
	client_top_6
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(6	)
	)
	inst_6(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[6]	),
		.s_axis_c_wvalid	(s_valid[6]	),
		.s_axis_c_wready	(s_ready[6]	),
		.s_axis_c_wlast		(s_last[6]	),
		.s_axis_c_tdest		(s_dest[6]	),
		.m_axis_c_wdata		(m_data[6]	),
		.m_axis_c_wvalid	(m_valid[6]	),
		.m_axis_c_wready	(m_ready[6]	),
		.m_axis_c_wlast		(m_last[6]	),
		.m_axis_c_tdest		(m_dest[6]	),
		.done			(done[6])	          
	);
	client_top_7
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(7	)
	)
	inst_7(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[7]	),
		.s_axis_c_wvalid	(s_valid[7]	),
		.s_axis_c_wready	(s_ready[7]	),
		.s_axis_c_wlast		(s_last[7]	),
		.s_axis_c_tdest		(s_dest[7]	),
		.m_axis_c_wdata		(m_data[7]	),
		.m_axis_c_wvalid	(m_valid[7]	),
		.m_axis_c_wready	(m_ready[7]	),
		.m_axis_c_wlast		(m_last[7]	),
		.m_axis_c_tdest		(m_dest[7]	),
		.done			(done[7])	          
	);
`endif

`ifdef Nis16
	client_top_0
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(0	)
	)
	inst_0(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[0]	),
		.s_axis_c_wvalid	(s_valid[0]	),
		.s_axis_c_wready	(s_ready[0]	),
		.s_axis_c_wlast		(s_last[0]	),
		.s_axis_c_tdest		(s_dest[0]	),
		.m_axis_c_wdata		(m_data[0]	),
		.m_axis_c_wvalid	(m_valid[0]	),
		.m_axis_c_wready	(m_ready[0]	),
		.m_axis_c_wlast		(m_last[0]	),
		.m_axis_c_tdest		(m_dest[0]	),
		.done			(done[0])	          
	);
	client_top_1
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(1	)
	)
	inst_1(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[1]	),
		.s_axis_c_wvalid	(s_valid[1]	),
		.s_axis_c_wready	(s_ready[1]	),
		.s_axis_c_wlast		(s_last[1]	),
		.s_axis_c_tdest		(s_dest[1]	),
		.m_axis_c_wdata		(m_data[1]	),
		.m_axis_c_wvalid	(m_valid[1]	),
		.m_axis_c_wready	(m_ready[1]	),
		.m_axis_c_wlast		(m_last[1]	),
		.m_axis_c_tdest		(m_dest[1]	),
		.done			(done[1])	          
	);
	client_top_2
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(2	)
	)
	inst_2(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[2]	),
		.s_axis_c_wvalid	(s_valid[2]	),
		.s_axis_c_wready	(s_ready[2]	),
		.s_axis_c_wlast		(s_last[2]	),
		.s_axis_c_tdest		(s_dest[2]	),
		.m_axis_c_wdata		(m_data[2]	),
		.m_axis_c_wvalid	(m_valid[2]	),
		.m_axis_c_wready	(m_ready[2]	),
		.m_axis_c_wlast		(m_last[2]	),
		.m_axis_c_tdest		(m_dest[2]	),
		.done			(done[2])	          
	);
	client_top_3
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(3	)
	)
	inst_3(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[3]	),
		.s_axis_c_wvalid	(s_valid[3]	),
		.s_axis_c_wready	(s_ready[3]	),
		.s_axis_c_wlast		(s_last[3]	),
		.s_axis_c_tdest		(s_dest[3]	),
		.m_axis_c_wdata		(m_data[3]	),
		.m_axis_c_wvalid	(m_valid[3]	),
		.m_axis_c_wready	(m_ready[3]	),
		.m_axis_c_wlast		(m_last[3]	),
		.m_axis_c_tdest		(m_dest[3]	),
		.done			(done[3])	          
	
	);
	client_top_4
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(4	)
	)
	inst_4(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[4]	),
		.s_axis_c_wvalid	(s_valid[4]	),
		.s_axis_c_wready	(s_ready[4]	),
		.s_axis_c_wlast		(s_last[4]	),
		.s_axis_c_tdest		(s_dest[4]	),
		.m_axis_c_wdata		(m_data[4]	),
		.m_axis_c_wvalid	(m_valid[4]	),
		.m_axis_c_wready	(m_ready[4]	),
		.m_axis_c_wlast		(m_last[4]	),
		.m_axis_c_tdest		(m_dest[4]	),
		.done			(done[4])	          
	
	);
	client_top_5
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(5	)
	)
	inst_5(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[5]	),
		.s_axis_c_wvalid	(s_valid[5]	),
		.s_axis_c_wready	(s_ready[5]	),
		.s_axis_c_wlast		(s_last[5]	),
		.s_axis_c_tdest		(s_dest[5]	),
		.m_axis_c_wdata		(m_data[5]	),
		.m_axis_c_wvalid	(m_valid[5]	),
		.m_axis_c_wready	(m_ready[5]	),
		.m_axis_c_wlast		(m_last[5]	),
		.m_axis_c_tdest		(m_dest[5]	),
		.done			(done[5])	          
	
	);
	client_top_6
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(6	)
	)
	inst_6(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[6]	),
		.s_axis_c_wvalid	(s_valid[6]	),
		.s_axis_c_wready	(s_ready[6]	),
		.s_axis_c_wlast		(s_last[6]	),
		.s_axis_c_tdest		(s_dest[6]	),
		.m_axis_c_wdata		(m_data[6]	),
		.m_axis_c_wvalid	(m_valid[6]	),
		.m_axis_c_wready	(m_ready[6]	),
		.m_axis_c_wlast		(m_last[6]	),
		.m_axis_c_tdest		(m_dest[6]	),
		.done			(done[6])	          
	
	);
	client_top_7
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(7	)
	)
	inst_7(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[7]	),
		.s_axis_c_wvalid	(s_valid[7]	),
		.s_axis_c_wready	(s_ready[7]	),
		.s_axis_c_wlast		(s_last[7]	),
		.s_axis_c_tdest		(s_dest[7]	),
		.m_axis_c_wdata		(m_data[7]	),
		.m_axis_c_wvalid	(m_valid[7]	),
		.m_axis_c_wready	(m_ready[7]	),
		.m_axis_c_wlast		(m_last[7]	),
		.m_axis_c_tdest		(m_dest[7]	),
		.done			(done[7])	          
	
	);
	client_top_8
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(8	)
	)
	inst_8(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[8]	),
		.s_axis_c_wvalid	(s_valid[8]	),
		.s_axis_c_wready	(s_ready[8]	),
		.s_axis_c_wlast		(s_last[8]	),
		.s_axis_c_tdest		(s_dest[8]	),
		.m_axis_c_wdata		(m_data[8]	),
		.m_axis_c_wvalid	(m_valid[8]	),
		.m_axis_c_wready	(m_ready[8]	),
		.m_axis_c_wlast		(m_last[8]	),
		.m_axis_c_tdest		(m_dest[8]	),
		.done			(done[8])	          
	
	);
	client_top_9
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(9	)
	)
	inst_9(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[9]	),
		.s_axis_c_wvalid	(s_valid[9]	),
		.s_axis_c_wready	(s_ready[9]	),
		.s_axis_c_wlast		(s_last[9]	),
		.s_axis_c_tdest		(s_dest[9]	),
		.m_axis_c_wdata		(m_data[9]	),
		.m_axis_c_wvalid	(m_valid[9]	),
		.m_axis_c_wready	(m_ready[9]	),
		.m_axis_c_wlast		(m_last[9]	),
		.m_axis_c_tdest		(m_dest[9]	),
		.done			(done[9])	          
	
	);
	client_top_10
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(10	)
	)
	inst_10(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[10]	),
		.s_axis_c_wvalid	(s_valid[10]	),
		.s_axis_c_wready	(s_ready[10]	),
		.s_axis_c_wlast		(s_last[10]	),
		.s_axis_c_tdest		(s_dest[10]	),
		.m_axis_c_wdata		(m_data[10]	),
		.m_axis_c_wvalid	(m_valid[10]	),
		.m_axis_c_wready	(m_ready[10]	),
		.m_axis_c_wlast		(m_last[10]	),
		.m_axis_c_tdest		(m_dest[10]	),
		.done			(done[10])	          
	
	);
	client_top_11
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(11	)
	)
	inst_11(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[11]	),
		.s_axis_c_wvalid	(s_valid[11]	),
		.s_axis_c_wready	(s_ready[11]	),
		.s_axis_c_wlast		(s_last[11]	),
		.s_axis_c_tdest		(s_dest[11]	),
		.m_axis_c_wdata		(m_data[11]	),
		.m_axis_c_wvalid	(m_valid[11]	),
		.m_axis_c_wready	(m_ready[11]	),
		.m_axis_c_wlast		(m_last[11]	),
		.m_axis_c_tdest		(m_dest[11]	),
		.done			(done[11])	          
	
	);
	client_top_12
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(12	)
	)
	inst_12(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[12]	),
		.s_axis_c_wvalid	(s_valid[12]	),
		.s_axis_c_wready	(s_ready[12]	),
		.s_axis_c_wlast		(s_last[12]	),
		.s_axis_c_tdest		(s_dest[12]	),
		.m_axis_c_wdata		(m_data[12]	),
		.m_axis_c_wvalid	(m_valid[12]	),
		.m_axis_c_wready	(m_ready[12]	),
		.m_axis_c_wlast		(m_last[12]	),
		.m_axis_c_tdest		(m_dest[12]	),
		.done			(done[12])	          
	
	);
	client_top_13
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(13	)
	)
	inst_13(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[13]	),
		.s_axis_c_wvalid	(s_valid[13]	),
		.s_axis_c_wready	(s_ready[13]	),
		.s_axis_c_wlast		(s_last[13]	),
		.s_axis_c_tdest		(s_dest[13]	),
		.m_axis_c_wdata		(m_data[13]	),
		.m_axis_c_wvalid	(m_valid[13]	),
		.m_axis_c_wready	(m_ready[13]	),
		.m_axis_c_wlast		(m_last[13]	),
		.m_axis_c_tdest		(m_dest[13]	),
		.done			(done[13])	          
	
	);
	client_top_14
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(14	)
	)
	inst_14(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[14]	),
		.s_axis_c_wvalid	(s_valid[14]	),
		.s_axis_c_wready	(s_ready[14]	),
		.s_axis_c_wlast		(s_last[14]	),
		.s_axis_c_tdest		(s_dest[14]	),
		.m_axis_c_wdata		(m_data[14]	),
		.m_axis_c_wvalid	(m_valid[14]	),
		.m_axis_c_wready	(m_ready[14]	),
		.m_axis_c_wlast		(m_last[14]	),
		.m_axis_c_tdest		(m_dest[14]	),
		.done			(done[14])	          
	
	);
	client_top_15
	#(
		.N	(N	),
		.D_W	(D_W	),
		.A_W	(A_W	),
		.WRAP 	(WRAP	),
		.PAT   	(PAT	),
		.RATE  	(RATE	),
		.LIMIT 	(LIMIT	),
		.SIGMA 	(SIGMA	),
		.posx 	(15	)
	)
	inst_15(
		.clk			(clk		),
		.rst			(rst		),
		.ce			(1'b1		),
		.cmd			(18		),
		.s_axis_c_wdata		(s_data[15]	),
		.s_axis_c_wvalid	(s_valid[15]	),
		.s_axis_c_wready	(s_ready[15]	),
		.s_axis_c_wlast		(s_last[15]	),
		.s_axis_c_tdest		(s_dest[15]	),
		.m_axis_c_wdata		(m_data[15]	),
		.m_axis_c_wvalid	(m_valid[15]	),
		.m_axis_c_wready	(m_ready[15]	),
		.m_axis_c_wlast		(m_last[15]	),
		.m_axis_c_tdest		(m_dest[15]	),
		.done			(done[15])	          
	
	);

`endif



`endif

(*dont_touch="true"*)wire	[31:0]		m_data	[0:N-1];
(*dont_touch="true"*)wire	[31:0]		s_data	[0:N-1];
(*dont_touch="true"*)wire	[3:0]		m_dest	[0:N-1];
(*dont_touch="true"*)wire	[3:0]		s_dest	[0:N-1];



`ifdef Nis2
assign  s_dest_0 = s_dest[0];
assign  s_dest_1 = s_dest[1];

assign  s_data_0 = s_data[0];
assign  s_data_1 = s_data[1];

assign  m_dest[0] = m_dest_0;
assign  m_dest[1] = m_dest_1;

assign  m_data[0] = m_data_0;
assign  m_data[1] = m_data_1;

`endif
`ifdef Nis4
assign  s_dest_0 = s_dest[0];
assign  s_dest_1 = s_dest[1];
assign  s_dest_2 = s_dest[2];
assign  s_dest_3 = s_dest[3];

assign  s_data_0 = s_data[0];
assign  s_data_1 = s_data[1];
assign  s_data_2 = s_data[2];
assign  s_data_3 = s_data[3];

assign  m_dest[0] = m_dest_0;
assign  m_dest[1] = m_dest_1;
assign  m_dest[2] = m_dest_2;
assign  m_dest[3] = m_dest_3;

assign  m_data[0] = m_data_0;
assign  m_data[1] = m_data_1;
assign  m_data[2] = m_data_2;
assign  m_data[3] = m_data_3;

`endif

`ifdef Nis8
assign  s_dest_0 = s_dest[0];
assign  s_dest_1 = s_dest[1];
assign  s_dest_2 = s_dest[2];
assign  s_dest_3 = s_dest[3];
assign  s_dest_4 = s_dest[4];
assign  s_dest_5 = s_dest[5];
assign  s_dest_6 = s_dest[6];
assign  s_dest_7 = s_dest[7];

assign  s_data_0 = s_data[0];
assign  s_data_1 = s_data[1];
assign  s_data_2 = s_data[2];
assign  s_data_3 = s_data[3];
assign  s_data_4 = s_data[4];
assign  s_data_5 = s_data[5];
assign  s_data_6 = s_data[6];
assign  s_data_7 = s_data[7];

assign  m_dest[0] = m_dest_0;
assign  m_dest[1] = m_dest_1;
assign  m_dest[2] = m_dest_2;
assign  m_dest[3] = m_dest_3;
assign  m_dest[4] = m_dest_4;
assign  m_dest[5] = m_dest_5;
assign  m_dest[6] = m_dest_6;
assign  m_dest[7] = m_dest_7;

assign  m_data[0] = m_data_0;
assign  m_data[1] = m_data_1;
assign  m_data[2] = m_data_2;
assign  m_data[3] = m_data_3;
assign  m_data[4] = m_data_4;
assign  m_data[5] = m_data_5;
assign  m_data[6] = m_data_6;
assign  m_data[7] = m_data_7;



`endif
`ifdef Nis16
assign  s_dest_0 = s_dest[0];
assign  s_dest_1 = s_dest[1];
assign  s_dest_2 = s_dest[2];
assign  s_dest_3 = s_dest[3];
assign  s_dest_4 = s_dest[4];
assign  s_dest_5 = s_dest[5];
assign  s_dest_6 = s_dest[6];
assign  s_dest_7 = s_dest[7];
assign  s_dest_8 = s_dest[8];
assign  s_dest_9 = s_dest[9];
assign  s_dest_10 = s_dest[10];
assign  s_dest_11 = s_dest[11];
assign  s_dest_12 = s_dest[12];
assign  s_dest_13 = s_dest[13];
assign  s_dest_14 = s_dest[14];
assign  s_dest_15 = s_dest[15];

assign  s_data_0 = s_data[0];
assign  s_data_1 = s_data[1];
assign  s_data_2 = s_data[2];
assign  s_data_3 = s_data[3];
assign  s_data_4 = s_data[4];
assign  s_data_5 = s_data[5];
assign  s_data_6 = s_data[6];
assign  s_data_7 = s_data[7];
assign  s_data_8 = s_data[8];
assign  s_data_9 = s_data[9];
assign  s_data_10 = s_data[10];
assign  s_data_11 = s_data[11];
assign  s_data_12 = s_data[12];
assign  s_data_13 = s_data[13];
assign  s_data_14 = s_data[14];
assign  s_data_15 = s_data[15];

assign  m_dest[0] = m_dest_0;
assign  m_dest[1] = m_dest_1;
assign  m_dest[2] = m_dest_2;
assign  m_dest[3] = m_dest_3;
assign  m_dest[4] = m_dest_4;
assign  m_dest[5] = m_dest_5;
assign  m_dest[6] = m_dest_6;
assign  m_dest[7] = m_dest_7;
assign  m_dest[8] = m_dest_8;
assign  m_dest[9] = m_dest_9;
assign  m_dest[10] = m_dest_10;
assign  m_dest[11] = m_dest_11;
assign  m_dest[12] = m_dest_12;
assign  m_dest[13] = m_dest_13;
assign  m_dest[14] = m_dest_14;
assign  m_dest[15] = m_dest_15;

assign  m_data[0] = m_data_0;
assign  m_data[1] = m_data_1;
assign  m_data[2] = m_data_2;
assign  m_data[3] = m_data_3;
assign  m_data[4] = m_data_4;
assign  m_data[5] = m_data_5;
assign  m_data[6] = m_data_6;
assign  m_data[7] = m_data_7;
assign  m_data[8] = m_data_8;
assign  m_data[9] = m_data_9;
assign  m_data[10] = m_data_10;
assign  m_data[11] = m_data_11;
assign  m_data[12] = m_data_12;
assign  m_data[13] = m_data_13;
assign  m_data[14] = m_data_14;
assign  m_data[15] = m_data_15;

`endif



`ifdef Nis2
axis_interconnect_1 inst2 (
  .ACLK					(clk),                          // input wire ACLK
  .ARESETN				(~rst),                    // input wire ARESETN
  .S00_AXIS_ACLK			(clk),        // input wire S00_AXIS_ACLK
  .S01_AXIS_ACLK			(clk),        // input wire S01_AXIS_ACLK
  
  .S00_AXIS_ARESETN			(~rst),  // input wire S00_AXIS_ARESETN
  .S01_AXIS_ARESETN			(~rst),  // input wire S01_AXIS_ARESETN
  
  .M00_AXIS_ACLK			(clk),        // input wire M00_AXIS_ACLK
  .M01_AXIS_ACLK			(clk),        // input wire M01_AXIS_ACLK
  
  .M00_AXIS_ARESETN			(~rst),  // input wire M00_AXIS_ARESETN
  .M01_AXIS_ARESETN			(~rst),  // input wire M01_AXIS_ARESETN
  
  .S00_AXIS_TVALID	(m_valid[0]),    // input wire S00_AXIS_TVALID
  .S01_AXIS_TVALID	(m_valid[1]),    // input wire S01_AXIS_TVALID
  
  .S00_AXIS_TREADY	(m_ready[0]), // output wire S00_AXIS_TREADY
  .S01_AXIS_TREADY	(m_ready[1]), // output wire S01_AXIS_TREADY
  
  .S00_AXIS_TDATA	(m_data[0]), // input wire [31 : 0] S00_AXIS_TDATA
  .S01_AXIS_TDATA	(m_data[1]), // input wire [31 : 0] S01_AXIS_TDATA
  
  .S00_AXIS_TLAST	(m_last[0]), // input wire S00_AXIS_TLAST
  .S01_AXIS_TLAST	(m_last[1]), // input wire S01_AXIS_TLAST
  
  .S00_AXIS_TDEST	(m_dest[0]), // input wire [3 : 0] S00_AXIS_TDEST
  .S01_AXIS_TDEST	(m_dest[1]), // input wire [3 : 0] S01_AXIS_TDEST  
  
  .M00_AXIS_TVALID	(s_valid[0]),    // input wire S00_AXIS_TVALID
  .M01_AXIS_TVALID	(s_valid[1]),    // input wire S01_AXIS_TVALID
  
  .M00_AXIS_TREADY	(s_ready[0]), // output wire S00_AXIS_TREADY
  .M01_AXIS_TREADY	(s_ready[1]), // output wire S01_AXIS_TREADY
  
  .M00_AXIS_TDATA	(s_data[0]), // input wire [31 : 0] S00_AXIS_TDATA
  .M01_AXIS_TDATA	(s_data[1]), // input wire [31 : 0] S01_AXIS_TDATA
  
  .M00_AXIS_TLAST	(s_last[0]), // input wire S00_AXIS_TLAST
  .M01_AXIS_TLAST	(s_last[1]), // input wire S01_AXIS_TLAST
  
  .M00_AXIS_TDEST	(s_dest[0]), // input wire [3 : 0] S00_AXIS_TDEST
  .M01_AXIS_TDEST	(s_dest[1]), // input wire [3 : 0] S01_AXIS_TDEST

  .S00_DECODE_ERR(S00_DECODE_ERR),      // output wire S00_DECODE_ERR
  .S01_DECODE_ERR(S01_DECODE_ERR)      // output wire S01_DECODE_ERR
);
`endif
`ifdef Nis4
axis_interconnect_1 inst4 (
  .ACLK					(clk),                          // input wire ACLK
  .ARESETN				(~rst),                    // input wire ARESETN
  .S00_AXIS_ACLK			(clk),        // input wire S00_AXIS_ACLK
  .S01_AXIS_ACLK			(clk),        // input wire S01_AXIS_ACLK
  .S02_AXIS_ACLK			(clk),        // input wire S02_AXIS_ACLK
  .S03_AXIS_ACLK			(clk),        // input wire S03_AXIS_ACLK
  
  .S00_AXIS_ARESETN			(~rst),  // input wire S00_AXIS_ARESETN
  .S01_AXIS_ARESETN			(~rst),  // input wire S01_AXIS_ARESETN
  .S02_AXIS_ARESETN			(~rst),  // input wire S02_AXIS_ARESETN
  .S03_AXIS_ARESETN			(~rst),  // input wire S03_AXIS_ARESETN
  
  .M00_AXIS_ACLK			(clk),        // input wire M00_AXIS_ACLK
  .M01_AXIS_ACLK			(clk),        // input wire M01_AXIS_ACLK
  .M02_AXIS_ACLK			(clk),        // input wire M02_AXIS_ACLK
  .M03_AXIS_ACLK			(clk),        // input wire M03_AXIS_ACLK
  
  .M00_AXIS_ARESETN			(~rst),  // input wire M00_AXIS_ARESETN
  .M01_AXIS_ARESETN			(~rst),  // input wire M01_AXIS_ARESETN
  .M02_AXIS_ARESETN			(~rst),  // input wire M02_AXIS_ARESETN
  .M03_AXIS_ARESETN			(~rst),  // input wire M03_AXIS_ARESETN
  
  .S00_AXIS_TVALID	(m_valid[0]),    // input wire S00_AXIS_TVALID
  .S01_AXIS_TVALID	(m_valid[1]),    // input wire S01_AXIS_TVALID
  .S02_AXIS_TVALID	(m_valid[2]),    // input wire S02_AXIS_TVALID
  .S03_AXIS_TVALID	(m_valid[3]),    // input wire S03_AXIS_TVALID
  
  .S00_AXIS_TREADY	(m_ready[0]), // output wire S00_AXIS_TREADY
  .S01_AXIS_TREADY	(m_ready[1]), // output wire S01_AXIS_TREADY
  .S02_AXIS_TREADY	(m_ready[2]), // output wire S02_AXIS_TREADY
  .S03_AXIS_TREADY	(m_ready[3]), // output wire S03_AXIS_TREADY
  
  .S00_AXIS_TDATA	(m_data[0]), // input wire [31 : 0] S00_AXIS_TDATA
  .S01_AXIS_TDATA	(m_data[1]), // input wire [31 : 0] S01_AXIS_TDATA
  .S02_AXIS_TDATA	(m_data[2]), // input wire [31 : 0] S02_AXIS_TDATA
  .S03_AXIS_TDATA	(m_data[3]), // input wire [31 : 0] S03_AXIS_TDATA
  
  .S00_AXIS_TLAST	(m_last[0]), // input wire S00_AXIS_TLAST
  .S01_AXIS_TLAST	(m_last[1]), // input wire S01_AXIS_TLAST
  .S02_AXIS_TLAST	(m_last[2]), // input wire S02_AXIS_TLAST
  .S03_AXIS_TLAST	(m_last[3]), // input wire S03_AXIS_TLAST
  
  .S00_AXIS_TDEST	(m_dest[0]), // input wire [3 : 0] S00_AXIS_TDEST
  .S01_AXIS_TDEST	(m_dest[1]), // input wire [3 : 0] S01_AXIS_TDEST
  .S02_AXIS_TDEST	(m_dest[2]), // input wire [3 : 0] S02_AXIS_TDEST
  .S03_AXIS_TDEST	(m_dest[3]), // input wire [3 : 0] S03_AXIS_TDEST
  
  
  .M00_AXIS_TVALID	(s_valid[0]),    // input wire S00_AXIS_TVALID
  .M01_AXIS_TVALID	(s_valid[1]),    // input wire S01_AXIS_TVALID
  .M02_AXIS_TVALID	(s_valid[2]),    // input wire S02_AXIS_TVALID
  .M03_AXIS_TVALID	(s_valid[3]),    // input wire S03_AXIS_TVALID
  
  .M00_AXIS_TREADY	(s_ready[0]), // output wire S00_AXIS_TREADY
  .M01_AXIS_TREADY	(s_ready[1]), // output wire S01_AXIS_TREADY
  .M02_AXIS_TREADY	(s_ready[2]), // output wire S02_AXIS_TREADY
  .M03_AXIS_TREADY	(s_ready[3]), // output wire S03_AXIS_TREADY
  
  .M00_AXIS_TDATA	(s_data[0]), // input wire [31 : 0] S00_AXIS_TDATA
  .M01_AXIS_TDATA	(s_data[1]), // input wire [31 : 0] S01_AXIS_TDATA
  .M02_AXIS_TDATA	(s_data[2]), // input wire [31 : 0] S02_AXIS_TDATA
  .M03_AXIS_TDATA	(s_data[3]), // input wire [31 : 0] S03_AXIS_TDATA
  
  .M00_AXIS_TLAST	(s_last[0]), // input wire S00_AXIS_TLAST
  .M01_AXIS_TLAST	(s_last[1]), // input wire S01_AXIS_TLAST
  .M02_AXIS_TLAST	(s_last[2]), // input wire S02_AXIS_TLAST
  .M03_AXIS_TLAST	(s_last[3]), // input wire S03_AXIS_TLAST
  
  .M00_AXIS_TDEST	(s_dest[0]), // input wire [3 : 0] S00_AXIS_TDEST
  .M01_AXIS_TDEST	(s_dest[1]), // input wire [3 : 0] S01_AXIS_TDEST
  .M02_AXIS_TDEST	(s_dest[2]), // input wire [3 : 0] S02_AXIS_TDEST
  .M03_AXIS_TDEST	(s_dest[3]), // input wire [3 : 0] S03_AXIS_TDEST
  
  .S00_DECODE_ERR(S00_DECODE_ERR),      // output wire S00_DECODE_ERR
  .S01_DECODE_ERR(S01_DECODE_ERR),      // output wire S01_DECODE_ERR
  .S02_DECODE_ERR(S02_DECODE_ERR),      // output wire S02_DECODE_ERR
  .S03_DECODE_ERR(S03_DECODE_ERR)      // output wire S03_DECODE_ERR
);
`endif

`ifdef Nis8
axis_interconnect_1 inst8 (
  .ACLK					(clk),                          // input wire ACLK
  .ARESETN				(~rst),                    // input wire ARESETN
  .S00_AXIS_ACLK			(clk),        // input wire S00_AXIS_ACLK
  .S01_AXIS_ACLK			(clk),        // input wire S01_AXIS_ACLK
  .S02_AXIS_ACLK			(clk),        // input wire S02_AXIS_ACLK
  .S03_AXIS_ACLK			(clk),        // input wire S03_AXIS_ACLK
  .S04_AXIS_ACLK			(clk),        // input wire S04_AXIS_ACLK
  .S05_AXIS_ACLK			(clk),        // input wire S05_AXIS_ACLK
  .S06_AXIS_ACLK			(clk),        // input wire S06_AXIS_ACLK
  .S07_AXIS_ACLK			(clk),        // input wire S07_AXIS_ACLK
  
  .S00_AXIS_ARESETN			(~rst),  // input wire S00_AXIS_ARESETN
  .S01_AXIS_ARESETN			(~rst),  // input wire S01_AXIS_ARESETN
  .S02_AXIS_ARESETN			(~rst),  // input wire S02_AXIS_ARESETN
  .S03_AXIS_ARESETN			(~rst),  // input wire S03_AXIS_ARESETN
  .S04_AXIS_ARESETN			(~rst),  // input wire S04_AXIS_ARESETN
  .S05_AXIS_ARESETN			(~rst),  // input wire S05_AXIS_ARESETN
  .S06_AXIS_ARESETN			(~rst),  // input wire S06_AXIS_ARESETN
  .S07_AXIS_ARESETN			(~rst),  // input wire S07_AXIS_ARESETN
  
  .M00_AXIS_ACLK			(clk),        // input wire M00_AXIS_ACLK
  .M01_AXIS_ACLK			(clk),        // input wire M01_AXIS_ACLK
  .M02_AXIS_ACLK			(clk),        // input wire M02_AXIS_ACLK
  .M03_AXIS_ACLK			(clk),        // input wire M03_AXIS_ACLK
  .M04_AXIS_ACLK			(clk),        // input wire M04_AXIS_ACLK
  .M05_AXIS_ACLK			(clk),        // input wire M05_AXIS_ACLK
  .M06_AXIS_ACLK			(clk),        // input wire M06_AXIS_ACLK
  .M07_AXIS_ACLK			(clk),        // input wire M07_AXIS_ACLK
  
  .M00_AXIS_ARESETN			(~rst),  // input wire M00_AXIS_ARESETN
  .M01_AXIS_ARESETN			(~rst),  // input wire M01_AXIS_ARESETN
  .M02_AXIS_ARESETN			(~rst),  // input wire M02_AXIS_ARESETN
  .M03_AXIS_ARESETN			(~rst),  // input wire M03_AXIS_ARESETN
  .M04_AXIS_ARESETN			(~rst),  // input wire M04_AXIS_ARESETN
  .M05_AXIS_ARESETN			(~rst),  // input wire M05_AXIS_ARESETN
  .M06_AXIS_ARESETN			(~rst),  // input wire M06_AXIS_ARESETN
  .M07_AXIS_ARESETN			(~rst),  // input wire M07_AXIS_ARESETN
  
  .S00_AXIS_TVALID	(m_valid[0]),    // input wire S00_AXIS_TVALID
  .S01_AXIS_TVALID	(m_valid[1]),    // input wire S01_AXIS_TVALID
  .S02_AXIS_TVALID	(m_valid[2]),    // input wire S02_AXIS_TVALID
  .S03_AXIS_TVALID	(m_valid[3]),    // input wire S03_AXIS_TVALID
  .S04_AXIS_TVALID	(m_valid[4]),    // input wire S04_AXIS_TVALID
  .S05_AXIS_TVALID	(m_valid[5]),    // input wire S05_AXIS_TVALID
  .S06_AXIS_TVALID	(m_valid[6]),    // input wire S06_AXIS_TVALID
  .S07_AXIS_TVALID	(m_valid[7]),    // input wire S07_AXIS_TVALID
  
  .S00_AXIS_TREADY	(m_ready[0]), // output wire S00_AXIS_TREADY
  .S01_AXIS_TREADY	(m_ready[1]), // output wire S01_AXIS_TREADY
  .S02_AXIS_TREADY	(m_ready[2]), // output wire S02_AXIS_TREADY
  .S03_AXIS_TREADY	(m_ready[3]), // output wire S03_AXIS_TREADY
  .S04_AXIS_TREADY	(m_ready[4]), // output wire S04_AXIS_TREADY
  .S05_AXIS_TREADY	(m_ready[5]), // output wire S05_AXIS_TREADY
  .S06_AXIS_TREADY	(m_ready[6]), // output wire S06_AXIS_TREADY
  .S07_AXIS_TREADY	(m_ready[7]), // output wire S07_AXIS_TREADY
  
  .S00_AXIS_TDATA	(m_data[0]), // input wire [31 : 0] S00_AXIS_TDATA
  .S01_AXIS_TDATA	(m_data[1]), // input wire [31 : 0] S01_AXIS_TDATA
  .S02_AXIS_TDATA	(m_data[2]), // input wire [31 : 0] S02_AXIS_TDATA
  .S03_AXIS_TDATA	(m_data[3]), // input wire [31 : 0] S03_AXIS_TDATA
  .S04_AXIS_TDATA	(m_data[4]), // input wire [31 : 0] S04_AXIS_TDATA
  .S05_AXIS_TDATA	(m_data[5]), // input wire [31 : 0] S05_AXIS_TDATA
  .S06_AXIS_TDATA	(m_data[6]), // input wire [31 : 0] S06_AXIS_TDATA
  .S07_AXIS_TDATA	(m_data[7]), // input wire [31 : 0] S07_AXIS_TDATA
  
  .S00_AXIS_TLAST	(m_last[0]), // input wire S00_AXIS_TLAST
  .S01_AXIS_TLAST	(m_last[1]), // input wire S01_AXIS_TLAST
  .S02_AXIS_TLAST	(m_last[2]), // input wire S02_AXIS_TLAST
  .S03_AXIS_TLAST	(m_last[3]), // input wire S03_AXIS_TLAST
  .S04_AXIS_TLAST	(m_last[4]), // input wire S04_AXIS_TLAST
  .S05_AXIS_TLAST	(m_last[5]), // input wire S05_AXIS_TLAST
  .S06_AXIS_TLAST	(m_last[6]), // input wire S06_AXIS_TLAST
  .S07_AXIS_TLAST	(m_last[7]), // input wire S07_AXIS_TLAST
  
  .S00_AXIS_TDEST	(m_dest[0]), // input wire [3 : 0] S00_AXIS_TDEST
  .S01_AXIS_TDEST	(m_dest[1]), // input wire [3 : 0] S01_AXIS_TDEST
  .S02_AXIS_TDEST	(m_dest[2]), // input wire [3 : 0] S02_AXIS_TDEST
  .S03_AXIS_TDEST	(m_dest[3]), // input wire [3 : 0] S03_AXIS_TDEST
  .S04_AXIS_TDEST	(m_dest[4]), // input wire [3 : 0] S04_AXIS_TDEST
  .S05_AXIS_TDEST	(m_dest[5]), // input wire [3 : 0] S05_AXIS_TDEST
  .S06_AXIS_TDEST	(m_dest[6]), // input wire [3 : 0] S06_AXIS_TDEST
  .S07_AXIS_TDEST	(m_dest[7]), // input wire [3 : 0] S07_AXIS_TDEST
  
  
  .M00_AXIS_TVALID	(s_valid[0]),    // input wire S00_AXIS_TVALID
  .M01_AXIS_TVALID	(s_valid[1]),    // input wire S01_AXIS_TVALID
  .M02_AXIS_TVALID	(s_valid[2]),    // input wire S02_AXIS_TVALID
  .M03_AXIS_TVALID	(s_valid[3]),    // input wire S03_AXIS_TVALID
  .M04_AXIS_TVALID	(s_valid[4]),    // input wire S04_AXIS_TVALID
  .M05_AXIS_TVALID	(s_valid[5]),    // input wire S05_AXIS_TVALID
  .M06_AXIS_TVALID	(s_valid[6]),    // input wire S06_AXIS_TVALID
  .M07_AXIS_TVALID	(s_valid[7]),    // input wire S07_AXIS_TVALID
  
  .M00_AXIS_TREADY	(s_ready[0]), // output wire S00_AXIS_TREADY
  .M01_AXIS_TREADY	(s_ready[1]), // output wire S01_AXIS_TREADY
  .M02_AXIS_TREADY	(s_ready[2]), // output wire S02_AXIS_TREADY
  .M03_AXIS_TREADY	(s_ready[3]), // output wire S03_AXIS_TREADY
  .M04_AXIS_TREADY	(s_ready[4]), // output wire S04_AXIS_TREADY
  .M05_AXIS_TREADY	(s_ready[5]), // output wire S05_AXIS_TREADY
  .M06_AXIS_TREADY	(s_ready[6]), // output wire S06_AXIS_TREADY
  .M07_AXIS_TREADY	(s_ready[7]), // output wire S07_AXIS_TREADY
  
  .M00_AXIS_TDATA	(s_data[0]), // input wire [31 : 0] S00_AXIS_TDATA
  .M01_AXIS_TDATA	(s_data[1]), // input wire [31 : 0] S01_AXIS_TDATA
  .M02_AXIS_TDATA	(s_data[2]), // input wire [31 : 0] S02_AXIS_TDATA
  .M03_AXIS_TDATA	(s_data[3]), // input wire [31 : 0] S03_AXIS_TDATA
  .M04_AXIS_TDATA	(s_data[4]), // input wire [31 : 0] S04_AXIS_TDATA
  .M05_AXIS_TDATA	(s_data[5]), // input wire [31 : 0] S05_AXIS_TDATA
  .M06_AXIS_TDATA	(s_data[6]), // input wire [31 : 0] S06_AXIS_TDATA
  .M07_AXIS_TDATA	(s_data[7]), // input wire [31 : 0] S07_AXIS_TDATA
  
  .M00_AXIS_TLAST	(s_last[0]), // input wire S00_AXIS_TLAST
  .M01_AXIS_TLAST	(s_last[1]), // input wire S01_AXIS_TLAST
  .M02_AXIS_TLAST	(s_last[2]), // input wire S02_AXIS_TLAST
  .M03_AXIS_TLAST	(s_last[3]), // input wire S03_AXIS_TLAST
  .M04_AXIS_TLAST	(s_last[4]), // input wire S04_AXIS_TLAST
  .M05_AXIS_TLAST	(s_last[5]), // input wire S05_AXIS_TLAST
  .M06_AXIS_TLAST	(s_last[6]), // input wire S06_AXIS_TLAST
  .M07_AXIS_TLAST	(s_last[7]), // input wire S07_AXIS_TLAST
  
  .M00_AXIS_TDEST	(s_dest[0]), // input wire [3 : 0] S00_AXIS_TDEST
  .M01_AXIS_TDEST	(s_dest[1]), // input wire [3 : 0] S01_AXIS_TDEST
  .M02_AXIS_TDEST	(s_dest[2]), // input wire [3 : 0] S02_AXIS_TDEST
  .M03_AXIS_TDEST	(s_dest[3]), // input wire [3 : 0] S03_AXIS_TDEST
  .M04_AXIS_TDEST	(s_dest[4]), // input wire [3 : 0] S04_AXIS_TDEST
  .M05_AXIS_TDEST	(s_dest[5]), // input wire [3 : 0] S05_AXIS_TDEST
  .M06_AXIS_TDEST	(s_dest[6]), // input wire [3 : 0] S06_AXIS_TDEST
  .M07_AXIS_TDEST	(s_dest[7]), // input wire [3 : 0] S07_AXIS_TDEST
  
  .S00_DECODE_ERR(S00_DECODE_ERR),      // output wire S00_DECODE_ERR
  .S01_DECODE_ERR(S01_DECODE_ERR),      // output wire S01_DECODE_ERR
  .S02_DECODE_ERR(S02_DECODE_ERR),      // output wire S02_DECODE_ERR
  .S03_DECODE_ERR(S03_DECODE_ERR),      // output wire S03_DECODE_ERR
  .S04_DECODE_ERR(S04_DECODE_ERR),      // output wire S04_DECODE_ERR
  .S05_DECODE_ERR(S05_DECODE_ERR),      // output wire S05_DECODE_ERR
  .S06_DECODE_ERR(S06_DECODE_ERR),      // output wire S06_DECODE_ERR
  .S07_DECODE_ERR(S07_DECODE_ERR)      // output wire S07_DECODE_ERR
);
`endif
`ifdef Nis16
axis_interconnect_1 inst16 (
  .ACLK					(clk),                          // input wire ACLK
  .ARESETN				(~rst),                    // input wire ARESETN
  .S00_AXIS_ACLK			(clk),        // input wire S00_AXIS_ACLK
  .S01_AXIS_ACLK			(clk),        // input wire S01_AXIS_ACLK
  .S02_AXIS_ACLK			(clk),        // input wire S02_AXIS_ACLK
  .S03_AXIS_ACLK			(clk),        // input wire S03_AXIS_ACLK
  .S04_AXIS_ACLK			(clk),        // input wire S04_AXIS_ACLK
  .S05_AXIS_ACLK			(clk),        // input wire S05_AXIS_ACLK
  .S06_AXIS_ACLK			(clk),        // input wire S06_AXIS_ACLK
  .S07_AXIS_ACLK			(clk),        // input wire S07_AXIS_ACLK
  .S08_AXIS_ACLK			(clk),        // input wire S08_AXIS_ACLK
  .S09_AXIS_ACLK			(clk),        // input wire S09_AXIS_ACLK
  .S10_AXIS_ACLK			(clk),        // input wire S10_AXIS_ACLK
  .S11_AXIS_ACLK			(clk),        // input wire S11_AXIS_ACLK
  .S12_AXIS_ACLK			(clk),        // input wire S12_AXIS_ACLK
  .S13_AXIS_ACLK			(clk),        // input wire S13_AXIS_ACLK
  .S14_AXIS_ACLK			(clk),        // input wire S14_AXIS_ACLK
  .S15_AXIS_ACLK			(clk),        // input wire S15_AXIS_ACLK
  .S00_AXIS_ARESETN			(~rst),  // input wire S00_AXIS_ARESETN
  .S01_AXIS_ARESETN			(~rst),  // input wire S01_AXIS_ARESETN
  .S02_AXIS_ARESETN			(~rst),  // input wire S02_AXIS_ARESETN
  .S03_AXIS_ARESETN			(~rst),  // input wire S03_AXIS_ARESETN
  .S04_AXIS_ARESETN			(~rst),  // input wire S04_AXIS_ARESETN
  .S05_AXIS_ARESETN			(~rst),  // input wire S05_AXIS_ARESETN
  .S06_AXIS_ARESETN			(~rst),  // input wire S06_AXIS_ARESETN
  .S07_AXIS_ARESETN			(~rst),  // input wire S07_AXIS_ARESETN
  .S08_AXIS_ARESETN			(~rst),  // input wire S08_AXIS_ARESETN
  .S09_AXIS_ARESETN			(~rst),  // input wire S09_AXIS_ARESETN
  .S10_AXIS_ARESETN			(~rst),  // input wire S10_AXIS_ARESETN
  .S11_AXIS_ARESETN			(~rst),  // input wire S11_AXIS_ARESETN
  .S12_AXIS_ARESETN			(~rst),  // input wire S12_AXIS_ARESETN
  .S13_AXIS_ARESETN			(~rst),  // input wire S13_AXIS_ARESETN
  .S14_AXIS_ARESETN			(~rst),  // input wire S14_AXIS_ARESETN
  .S15_AXIS_ARESETN			(~rst),  // input wire S15_AXIS_ARESETN
  .M00_AXIS_ACLK			(clk),        // input wire M00_AXIS_ACLK
  .M01_AXIS_ACLK			(clk),        // input wire M01_AXIS_ACLK
  .M02_AXIS_ACLK			(clk),        // input wire M02_AXIS_ACLK
  .M03_AXIS_ACLK			(clk),        // input wire M03_AXIS_ACLK
  .M04_AXIS_ACLK			(clk),        // input wire M04_AXIS_ACLK
  .M05_AXIS_ACLK			(clk),        // input wire M05_AXIS_ACLK
  .M06_AXIS_ACLK			(clk),        // input wire M06_AXIS_ACLK
  .M07_AXIS_ACLK			(clk),        // input wire M07_AXIS_ACLK
  .M08_AXIS_ACLK			(clk),        // input wire M08_AXIS_ACLK
  .M09_AXIS_ACLK			(clk),        // input wire M09_AXIS_ACLK
  .M10_AXIS_ACLK			(clk),        // input wire M10_AXIS_ACLK
  .M11_AXIS_ACLK			(clk),        // input wire M11_AXIS_ACLK
  .M12_AXIS_ACLK			(clk),        // input wire M12_AXIS_ACLK
  .M13_AXIS_ACLK			(clk),        // input wire M13_AXIS_ACLK
  .M14_AXIS_ACLK			(clk),        // input wire M14_AXIS_ACLK
  .M15_AXIS_ACLK			(clk),        // input wire M15_AXIS_ACLK
  .M00_AXIS_ARESETN			(~rst),  // input wire M00_AXIS_ARESETN
  .M01_AXIS_ARESETN			(~rst),  // input wire M01_AXIS_ARESETN
  .M02_AXIS_ARESETN			(~rst),  // input wire M02_AXIS_ARESETN
  .M03_AXIS_ARESETN			(~rst),  // input wire M03_AXIS_ARESETN
  .M04_AXIS_ARESETN			(~rst),  // input wire M04_AXIS_ARESETN
  .M05_AXIS_ARESETN			(~rst),  // input wire M05_AXIS_ARESETN
  .M06_AXIS_ARESETN			(~rst),  // input wire M06_AXIS_ARESETN
  .M07_AXIS_ARESETN			(~rst),  // input wire M07_AXIS_ARESETN
  .M08_AXIS_ARESETN			(~rst),  // input wire M08_AXIS_ARESETN
  .M09_AXIS_ARESETN			(~rst),  // input wire M09_AXIS_ARESETN
  .M10_AXIS_ARESETN			(~rst),  // input wire M10_AXIS_ARESETN
  .M11_AXIS_ARESETN			(~rst),  // input wire M11_AXIS_ARESETN
  .M12_AXIS_ARESETN			(~rst),  // input wire M12_AXIS_ARESETN
  .M13_AXIS_ARESETN			(~rst),  // input wire M13_AXIS_ARESETN
  .M14_AXIS_ARESETN			(~rst),  // input wire M14_AXIS_ARESETN
  .M15_AXIS_ARESETN			(~rst),  // input wire M15_AXIS_ARESETN
  
  .S00_AXIS_TVALID	(m_valid[0]),    // input wire S00_AXIS_TVALID
  .S01_AXIS_TVALID	(m_valid[1]),    // input wire S01_AXIS_TVALID
  .S02_AXIS_TVALID	(m_valid[2]),    // input wire S02_AXIS_TVALID
  .S03_AXIS_TVALID	(m_valid[3]),    // input wire S03_AXIS_TVALID
  .S04_AXIS_TVALID	(m_valid[4]),    // input wire S04_AXIS_TVALID
  .S05_AXIS_TVALID	(m_valid[5]),    // input wire S05_AXIS_TVALID
  .S06_AXIS_TVALID	(m_valid[6]),    // input wire S06_AXIS_TVALID
  .S07_AXIS_TVALID	(m_valid[7]),    // input wire S07_AXIS_TVALID
  .S08_AXIS_TVALID	(m_valid[8]),    // input wire S08_AXIS_TVALID
  .S09_AXIS_TVALID	(m_valid[9]),    // input wire S09_AXIS_TVALID
  .S10_AXIS_TVALID	(m_valid[10]),    // input wire S10_AXIS_TVALID
  .S11_AXIS_TVALID	(m_valid[11]),    // input wire S11_AXIS_TVALID
  .S12_AXIS_TVALID	(m_valid[12]),    // input wire S12_AXIS_TVALID
  .S13_AXIS_TVALID	(m_valid[13]),    // input wire S13_AXIS_TVALID
  .S14_AXIS_TVALID	(m_valid[14]),    // input wire S14_AXIS_TVALID
  .S15_AXIS_TVALID	(m_valid[15]),    // input wire S15_AXIS_TVALID
  
  .S00_AXIS_TREADY	(m_ready[0]), // output wire S00_AXIS_TREADY
  .S01_AXIS_TREADY	(m_ready[1]), // output wire S01_AXIS_TREADY
  .S02_AXIS_TREADY	(m_ready[2]), // output wire S02_AXIS_TREADY
  .S03_AXIS_TREADY	(m_ready[3]), // output wire S03_AXIS_TREADY
  .S04_AXIS_TREADY	(m_ready[4]), // output wire S04_AXIS_TREADY
  .S05_AXIS_TREADY	(m_ready[5]), // output wire S05_AXIS_TREADY
  .S06_AXIS_TREADY	(m_ready[6]), // output wire S06_AXIS_TREADY
  .S07_AXIS_TREADY	(m_ready[7]), // output wire S07_AXIS_TREADY
  .S08_AXIS_TREADY	(m_ready[8]), // output wire S08_AXIS_TREADY
  .S09_AXIS_TREADY	(m_ready[9]), // output wire S09_AXIS_TREADY
  .S10_AXIS_TREADY	(m_ready[10]),// output wire S10_AXIS_TREADY
  .S11_AXIS_TREADY	(m_ready[11]),// output wire S11_AXIS_TREADY
  .S12_AXIS_TREADY	(m_ready[12]),// output wire S12_AXIS_TREADY
  .S13_AXIS_TREADY	(m_ready[13]),// output wire S13_AXIS_TREADY
  .S14_AXIS_TREADY	(m_ready[14]),// output wire S14_AXIS_TREADY
  .S15_AXIS_TREADY	(m_ready[15]),// output wire S15_AXIS_TREADY
  
  .S00_AXIS_TDATA	(m_data[0]), // input wire [31 : 0] S00_AXIS_TDATA
  .S01_AXIS_TDATA	(m_data[1]), // input wire [31 : 0] S01_AXIS_TDATA
  .S02_AXIS_TDATA	(m_data[2]), // input wire [31 : 0] S02_AXIS_TDATA
  .S03_AXIS_TDATA	(m_data[3]), // input wire [31 : 0] S03_AXIS_TDATA
  .S04_AXIS_TDATA	(m_data[4]), // input wire [31 : 0] S04_AXIS_TDATA
  .S05_AXIS_TDATA	(m_data[5]), // input wire [31 : 0] S05_AXIS_TDATA
  .S06_AXIS_TDATA	(m_data[6]), // input wire [31 : 0] S06_AXIS_TDATA
  .S07_AXIS_TDATA	(m_data[7]), // input wire [31 : 0] S07_AXIS_TDATA
  .S08_AXIS_TDATA	(m_data[8]), // input wire [31 : 0] S08_AXIS_TDATA
  .S09_AXIS_TDATA	(m_data[9]), // input wire [31 : 0] S09_AXIS_TDATA
  .S10_AXIS_TDATA	(m_data[10]),// input wire [31 : 0] S10_AXIS_TDATA
  .S11_AXIS_TDATA	(m_data[11]),// input wire [31 : 0] S11_AXIS_TDATA
  .S12_AXIS_TDATA	(m_data[12]),// input wire [31 : 0] S12_AXIS_TDATA
  .S13_AXIS_TDATA	(m_data[13]),// input wire [31 : 0] S13_AXIS_TDATA
  .S14_AXIS_TDATA	(m_data[14]),// input wire [31 : 0] S14_AXIS_TDATA
  .S15_AXIS_TDATA	(m_data[15]),// input wire [31 : 0] S15_AXIS_TDATA
  
  .S00_AXIS_TLAST	(m_last[0]), // input wire S00_AXIS_TLAST
  .S01_AXIS_TLAST	(m_last[1]), // input wire S01_AXIS_TLAST
  .S02_AXIS_TLAST	(m_last[2]), // input wire S02_AXIS_TLAST
  .S03_AXIS_TLAST	(m_last[3]), // input wire S03_AXIS_TLAST
  .S04_AXIS_TLAST	(m_last[4]), // input wire S04_AXIS_TLAST
  .S05_AXIS_TLAST	(m_last[5]), // input wire S05_AXIS_TLAST
  .S06_AXIS_TLAST	(m_last[6]), // input wire S06_AXIS_TLAST
  .S07_AXIS_TLAST	(m_last[7]), // input wire S07_AXIS_TLAST
  .S08_AXIS_TLAST	(m_last[8]), // input wire S08_AXIS_TLAST
  .S09_AXIS_TLAST	(m_last[9]), // input wire S09_AXIS_TLAST
  .S10_AXIS_TLAST	(m_last[10]),// input wire S10_AXIS_TLAST
  .S11_AXIS_TLAST	(m_last[11]),// input wire S11_AXIS_TLAST
  .S12_AXIS_TLAST	(m_last[12]),// input wire S12_AXIS_TLAST
  .S13_AXIS_TLAST	(m_last[13]),// input wire S13_AXIS_TLAST
  .S14_AXIS_TLAST	(m_last[14]),// input wire S14_AXIS_TLAST
  .S15_AXIS_TLAST	(m_last[15]),// input wire S15_AXIS_TLAST
  
  .S00_AXIS_TDEST	(m_dest[0]), // input wire [3 : 0] S00_AXIS_TDEST
  .S01_AXIS_TDEST	(m_dest[1]), // input wire [3 : 0] S01_AXIS_TDEST
  .S02_AXIS_TDEST	(m_dest[2]), // input wire [3 : 0] S02_AXIS_TDEST
  .S03_AXIS_TDEST	(m_dest[3]), // input wire [3 : 0] S03_AXIS_TDEST
  .S04_AXIS_TDEST	(m_dest[4]), // input wire [3 : 0] S04_AXIS_TDEST
  .S05_AXIS_TDEST	(m_dest[5]), // input wire [3 : 0] S05_AXIS_TDEST
  .S06_AXIS_TDEST	(m_dest[6]), // input wire [3 : 0] S06_AXIS_TDEST
  .S07_AXIS_TDEST	(m_dest[7]), // input wire [3 : 0] S07_AXIS_TDEST
  .S08_AXIS_TDEST	(m_dest[8]), // input wire [3 : 0] S08_AXIS_TDEST
  .S09_AXIS_TDEST	(m_dest[9]), // input wire [3 : 0] S09_AXIS_TDEST
  .S10_AXIS_TDEST	(m_dest[10]),// input wire [3 : 0] S10_AXIS_TDEST
  .S11_AXIS_TDEST	(m_dest[11]),// input wire [3 : 0] S11_AXIS_TDEST
  .S12_AXIS_TDEST	(m_dest[12]),// input wire [3 : 0] S12_AXIS_TDEST
  .S13_AXIS_TDEST	(m_dest[13]),// input wire [3 : 0] S13_AXIS_TDEST
  .S14_AXIS_TDEST	(m_dest[14]),// input wire [3 : 0] S14_AXIS_TDEST
  .S15_AXIS_TDEST	(m_dest[15]),// input wire [3 : 0] S15_AXIS_TDEST
  
  
  .M00_AXIS_TVALID	(s_valid[0]),    // input wire S00_AXIS_TVALID
  .M01_AXIS_TVALID	(s_valid[1]),    // input wire S01_AXIS_TVALID
  .M02_AXIS_TVALID	(s_valid[2]),    // input wire S02_AXIS_TVALID
  .M03_AXIS_TVALID	(s_valid[3]),    // input wire S03_AXIS_TVALID
  .M04_AXIS_TVALID	(s_valid[4]),    // input wire S04_AXIS_TVALID
  .M05_AXIS_TVALID	(s_valid[5]),    // input wire S05_AXIS_TVALID
  .M06_AXIS_TVALID	(s_valid[6]),    // input wire S06_AXIS_TVALID
  .M07_AXIS_TVALID	(s_valid[7]),    // input wire S07_AXIS_TVALID
  .M08_AXIS_TVALID	(s_valid[8]),    // input wire S08_AXIS_TVALID
  .M09_AXIS_TVALID	(s_valid[9]),    // input wire S09_AXIS_TVALID
  .M10_AXIS_TVALID	(s_valid[10]),    // input wire S10_AXIS_TVALID
  .M11_AXIS_TVALID	(s_valid[11]),    // input wire S11_AXIS_TVALID
  .M12_AXIS_TVALID	(s_valid[12]),    // input wire S12_AXIS_TVALID
  .M13_AXIS_TVALID	(s_valid[13]),    // input wire S13_AXIS_TVALID
  .M14_AXIS_TVALID	(s_valid[14]),    // input wire S14_AXIS_TVALID
  .M15_AXIS_TVALID	(s_valid[15]),    // input wire S15_AXIS_TVALID
  
  .M00_AXIS_TREADY	(s_ready[0]), // output wire S00_AXIS_TREADY
  .M01_AXIS_TREADY	(s_ready[1]), // output wire S01_AXIS_TREADY
  .M02_AXIS_TREADY	(s_ready[2]), // output wire S02_AXIS_TREADY
  .M03_AXIS_TREADY	(s_ready[3]), // output wire S03_AXIS_TREADY
  .M04_AXIS_TREADY	(s_ready[4]), // output wire S04_AXIS_TREADY
  .M05_AXIS_TREADY	(s_ready[5]), // output wire S05_AXIS_TREADY
  .M06_AXIS_TREADY	(s_ready[6]), // output wire S06_AXIS_TREADY
  .M07_AXIS_TREADY	(s_ready[7]), // output wire S07_AXIS_TREADY
  .M08_AXIS_TREADY	(s_ready[8]), // output wire S08_AXIS_TREADY
  .M09_AXIS_TREADY	(s_ready[9]), // output wire S09_AXIS_TREADY
  .M10_AXIS_TREADY	(s_ready[10]),// output wire S10_AXIS_TREADY
  .M11_AXIS_TREADY	(s_ready[11]),// output wire S11_AXIS_TREADY
  .M12_AXIS_TREADY	(s_ready[12]),// output wire S12_AXIS_TREADY
  .M13_AXIS_TREADY	(s_ready[13]),// output wire S13_AXIS_TREADY
  .M14_AXIS_TREADY	(s_ready[14]),// output wire S14_AXIS_TREADY
  .M15_AXIS_TREADY	(s_ready[15]),// output wire S15_AXIS_TREADY
  
  .M00_AXIS_TDATA	(s_data[0]), // input wire [31 : 0] S00_AXIS_TDATA
  .M01_AXIS_TDATA	(s_data[1]), // input wire [31 : 0] S01_AXIS_TDATA
  .M02_AXIS_TDATA	(s_data[2]), // input wire [31 : 0] S02_AXIS_TDATA
  .M03_AXIS_TDATA	(s_data[3]), // input wire [31 : 0] S03_AXIS_TDATA
  .M04_AXIS_TDATA	(s_data[4]), // input wire [31 : 0] S04_AXIS_TDATA
  .M05_AXIS_TDATA	(s_data[5]), // input wire [31 : 0] S05_AXIS_TDATA
  .M06_AXIS_TDATA	(s_data[6]), // input wire [31 : 0] S06_AXIS_TDATA
  .M07_AXIS_TDATA	(s_data[7]), // input wire [31 : 0] S07_AXIS_TDATA
  .M08_AXIS_TDATA	(s_data[8]), // input wire [31 : 0] S08_AXIS_TDATA
  .M09_AXIS_TDATA	(s_data[9]), // input wire [31 : 0] S09_AXIS_TDATA
  .M10_AXIS_TDATA	(s_data[10]),// input wire [31 : 0] S10_AXIS_TDATA
  .M11_AXIS_TDATA	(s_data[11]),// input wire [31 : 0] S11_AXIS_TDATA
  .M12_AXIS_TDATA	(s_data[12]),// input wire [31 : 0] S12_AXIS_TDATA
  .M13_AXIS_TDATA	(s_data[13]),// input wire [31 : 0] S13_AXIS_TDATA
  .M14_AXIS_TDATA	(s_data[14]),// input wire [31 : 0] S14_AXIS_TDATA
  .M15_AXIS_TDATA	(s_data[15]),// input wire [31 : 0] S15_AXIS_TDATA
  
  .M00_AXIS_TLAST	(s_last[0]), // input wire S00_AXIS_TLAST
  .M01_AXIS_TLAST	(s_last[1]), // input wire S01_AXIS_TLAST
  .M02_AXIS_TLAST	(s_last[2]), // input wire S02_AXIS_TLAST
  .M03_AXIS_TLAST	(s_last[3]), // input wire S03_AXIS_TLAST
  .M04_AXIS_TLAST	(s_last[4]), // input wire S04_AXIS_TLAST
  .M05_AXIS_TLAST	(s_last[5]), // input wire S05_AXIS_TLAST
  .M06_AXIS_TLAST	(s_last[6]), // input wire S06_AXIS_TLAST
  .M07_AXIS_TLAST	(s_last[7]), // input wire S07_AXIS_TLAST
  .M08_AXIS_TLAST	(s_last[8]), // input wire S08_AXIS_TLAST
  .M09_AXIS_TLAST	(s_last[9]), // input wire S09_AXIS_TLAST
  .M10_AXIS_TLAST	(s_last[10]),// input wire S10_AXIS_TLAST
  .M11_AXIS_TLAST	(s_last[11]),// input wire S11_AXIS_TLAST
  .M12_AXIS_TLAST	(s_last[12]),// input wire S12_AXIS_TLAST
  .M13_AXIS_TLAST	(s_last[13]),// input wire S13_AXIS_TLAST
  .M14_AXIS_TLAST	(s_last[14]),// input wire S14_AXIS_TLAST
  .M15_AXIS_TLAST	(s_last[15]),// input wire S15_AXIS_TLAST
  
  .M00_AXIS_TDEST	(s_dest[0]), // input wire [3 : 0] S00_AXIS_TDEST
  .M01_AXIS_TDEST	(s_dest[1]), // input wire [3 : 0] S01_AXIS_TDEST
  .M02_AXIS_TDEST	(s_dest[2]), // input wire [3 : 0] S02_AXIS_TDEST
  .M03_AXIS_TDEST	(s_dest[3]), // input wire [3 : 0] S03_AXIS_TDEST
  .M04_AXIS_TDEST	(s_dest[4]), // input wire [3 : 0] S04_AXIS_TDEST
  .M05_AXIS_TDEST	(s_dest[5]), // input wire [3 : 0] S05_AXIS_TDEST
  .M06_AXIS_TDEST	(s_dest[6]), // input wire [3 : 0] S06_AXIS_TDEST
  .M07_AXIS_TDEST	(s_dest[7]), // input wire [3 : 0] S07_AXIS_TDEST
  .M08_AXIS_TDEST	(s_dest[8]), // input wire [3 : 0] S08_AXIS_TDEST
  .M09_AXIS_TDEST	(s_dest[9]), // input wire [3 : 0] S09_AXIS_TDEST
  .M10_AXIS_TDEST	(s_dest[10]),// input wire [3 : 0] S10_AXIS_TDEST
  .M11_AXIS_TDEST	(s_dest[11]),// input wire [3 : 0] S11_AXIS_TDEST
  .M12_AXIS_TDEST	(s_dest[12]),// input wire [3 : 0] S12_AXIS_TDEST
  .M13_AXIS_TDEST	(s_dest[13]),// input wire [3 : 0] S13_AXIS_TDEST
  .M14_AXIS_TDEST	(s_dest[14]),// input wire [3 : 0] S14_AXIS_TDEST
  .M15_AXIS_TDEST	(s_dest[15]),// input wire [3 : 0] S15_AXIS_TDEST
  
  .S00_DECODE_ERR(S00_DECODE_ERR),      // output wire S00_DECODE_ERR
  .S01_DECODE_ERR(S01_DECODE_ERR),      // output wire S01_DECODE_ERR
  .S02_DECODE_ERR(S02_DECODE_ERR),      // output wire S02_DECODE_ERR
  .S03_DECODE_ERR(S03_DECODE_ERR),      // output wire S03_DECODE_ERR
  .S04_DECODE_ERR(S04_DECODE_ERR),      // output wire S04_DECODE_ERR
  .S05_DECODE_ERR(S05_DECODE_ERR),      // output wire S05_DECODE_ERR
  .S06_DECODE_ERR(S06_DECODE_ERR),      // output wire S06_DECODE_ERR
  .S07_DECODE_ERR(S07_DECODE_ERR),      // output wire S07_DECODE_ERR
  .S08_DECODE_ERR(S08_DECODE_ERR),      // output wire S08_DECODE_ERR
  .S09_DECODE_ERR(S09_DECODE_ERR),      // output wire S09_DECODE_ERR
  .S10_DECODE_ERR(S10_DECODE_ERR),      // output wire S10_DECODE_ERR
  .S11_DECODE_ERR(S11_DECODE_ERR),      // output wire S11_DECODE_ERR
  .S12_DECODE_ERR(S12_DECODE_ERR),      // output wire S12_DECODE_ERR
  .S13_DECODE_ERR(S13_DECODE_ERR),      // output wire S13_DECODE_ERR
  .S14_DECODE_ERR(S14_DECODE_ERR),      // output wire S14_DECODE_ERR
  .S15_DECODE_ERR(S15_DECODE_ERR)      // output wire S15_DECODE_ERR
);
`endif
endmodule
