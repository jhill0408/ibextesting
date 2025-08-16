
module pi_switch_top
#
(
	parameter	N	= 2,			//number of clients
	parameter	WRAP	= 1,			//crossbar?
	parameter	A_W	= $clog2(N) + 1, 	//addr width
	parameter	D_W	= 32,			//data width
	parameter	posl	= 0,			//which level
	parameter	posx	= 0,		//which position
	parameter	DEBUG	= 1,
	parameter	FD	= 10,
	parameter	HR	= 4
)
(
	input  wire 			clk,		// clock
	input  wire 			rst,		// reset
	input  wire 			ce,		// clock enable
	
	input  	wire	[A_W+D_W-1:0] 	s_axis_l_wdata	,	
	output	wire			s_axis_l_wready	,
	input	wire			s_axis_l_wvalid	,
	input	wire			s_axis_l_wlast	,
	
	input  	wire	[A_W+D_W-1:0] 	s_axis_r_wdata	,
	output	wire			s_axis_r_wready	,
	input	wire			s_axis_r_wvalid	,
	input	wire			s_axis_r_wlast	,
	
	input  	wire	[A_W+D_W-1:0] 	s_axis_u0_wdata	,
	output	wire			s_axis_u0_wready, 
	input	wire			s_axis_u0_wvalid, 
	input	wire			s_axis_u0_wlast	,

	input  	wire	[A_W+D_W-1:0] 	s_axis_u1_wdata	,
	output	wire			s_axis_u1_wready, 
	input	wire			s_axis_u1_wvalid, 
	input	wire			s_axis_u1_wlast	,

	output 	wire	[A_W+D_W-1:0] 	m_axis_l_wdata	,
	input	wire			m_axis_l_wready	,
	output	wire			m_axis_l_wvalid	,
	output	wire			m_axis_l_wlast	,	

	output 	wire	[A_W+D_W-1:0] 	m_axis_r_wdata	,
	input	wire			m_axis_r_wready	,
	output	wire			m_axis_r_wvalid	,
	output	wire			m_axis_r_wlast	,	

	output 	wire	[A_W+D_W-1:0] 	m_axis_u0_wdata	,
	input	wire			m_axis_u0_wready,
	output	wire			m_axis_u0_wvalid,
	output	wire			m_axis_u0_wlast	,	

	output 	wire	[A_W+D_W-1:0] 	m_axis_u1_wdata	,
	input	wire			m_axis_u1_wready,
	output	wire			m_axis_u1_wvalid,
	output	wire			m_axis_u1_wlast	,	
	output 	wire 			done		// done
);
`ifdef HYPERFLEX

reg	[A_W+D_W:0]	s_axis_l_wdata_hr	[HR-1:0];
reg			s_axis_l_wvalid_hr	[HR-1:0];
reg			s_axis_l_wready_hr	[HR-1:0];

wire	[A_W+D_W:0]	pi_o_d_l;
wire			pi_o_v_l;
wire			pi_o_b_l;

assign	m_axis_l_wdata	= pi_o_d_l[A_W+D_W-1:0];
assign	m_axis_l_wvalid	= pi_o_v_l;
assign	pi_o_b_l	= ~m_axis_l_wready;
assign	m_axis_l_wlast	= pi_o_d_l[A_W+D_W];

assign	s_axis_l_wready	= s_axis_l_wready_hr[HR-1];

integer hr_l;
integer now=0;

always@(posedge clk)
begin
	now <= now + 1;
	s_axis_l_wdata_hr[0]	<= {s_axis_l_wlast,s_axis_l_wdata};
	s_axis_l_wvalid_hr[0]	<= s_axis_l_wvalid;
	s_axis_l_wready_hr[0]	<= ~l_fifo_full;
	for(hr_l=0;hr_l<HR-1;hr_l=hr_l+1)
	begin
		s_axis_l_wdata_hr[hr_l+1]	<= s_axis_l_wdata_hr[hr_l];
		s_axis_l_wvalid_hr[hr_l+1]	<= s_axis_l_wvalid_hr[hr_l];
		s_axis_l_wready_hr[hr_l+1]	<= s_axis_l_wready_hr[hr_l];
	end

end


wire			l_fifo_empty;
wire			l_fifo_done;
wire			l_fifo_full;

wire	[A_W+D_W:0]	pi_i_d_l;
wire			pi_i_v_l;
wire			pi_i_bp_l;

`ifdef SIM
fwft_fifo 
#(
	.fifo_dw	(A_W+D_W+1),
	.fifo_depth	(FD+2*HR),
	.LOC		("w"),
	.HR		(HR)
)
l_fifo
(
	.clk		(clk				),
	.rst		(rst				),
	.d_in		(s_axis_l_wdata_hr[HR-1]	),//
	.wr_en		(s_axis_l_wvalid_hr[HR-1]	),//
	.full_early		(l_fifo_full			),//
	.d_out		(pi_i_d_l			),//
	.d_valid_out	(pi_i_v_l			),//
	.rd_en		(~pi_i_bp_l & ~l_fifo_empty	),//
	.empty		(l_fifo_empty			),//
	.done		(l_fifo_done			) //
);
`endif
`ifdef XLNXSRLFIFO
fifo_generator_1 l_fifo
(
	.clk		(clk				),
	.srst		(rst				),
	.din		({s_axis_l_wvalid,s_axis_l_wdata_hr[HR-1]}	),//
	.wr_en		(s_axis_l_wvalid_hr[HR-1]	),//
	.full		(l_fifo_full			),//
	.dout		({pi_i_v_l,pi_i_d_l}			),//
	.rd_en		(~pi_i_bp_l & ~l_fifo_empty	),//
	.empty		(l_fifo_empty			)//
//	.done		(l_fifo_done			) //
);
`endif
reg	[A_W+D_W:0]	s_axis_r_wdata_hr	[HR-1:0];
reg			s_axis_r_wvalid_hr	[HR-1:0];
reg			s_axis_r_wready_hr	[HR-1:0];

wire	[A_W+D_W:0]	pi_o_d_r;
wire			pi_o_v_r;
wire			pi_o_b_r;

assign	m_axis_r_wdata	= pi_o_d_r[A_W+D_W-1:0];
assign	m_axis_r_wvalid	= pi_o_v_r;
assign	pi_o_b_r	= ~m_axis_r_wready;
assign	m_axis_r_wlast	= pi_o_d_r[A_W+D_W];

assign	s_axis_r_wready	= s_axis_r_wready_hr[HR-1];

integer hr_r;

always@(posedge clk)
begin
	s_axis_r_wdata_hr[0]	<= {s_axis_r_wlast,s_axis_r_wdata};
	s_axis_r_wvalid_hr[0]	<= s_axis_r_wvalid;
	s_axis_r_wready_hr[0]	<= ~r_fifo_full;
	for(hr_r=0;hr_r<HR-1;hr_r=hr_r+1)
	begin
		s_axis_r_wdata_hr[hr_r+1]	<= s_axis_r_wdata_hr[hr_r];
		s_axis_r_wvalid_hr[hr_r+1]	<= s_axis_r_wvalid_hr[hr_r];
		s_axis_r_wready_hr[hr_r+1]	<= s_axis_r_wready_hr[hr_r];
	end

end


wire			r_fifo_empty;
wire			r_fifo_done;
wire			r_fifo_full;

wire	[A_W+D_W:0]	pi_i_d_r;
wire			pi_i_v_r;
wire			pi_i_bp_r;
`ifdef SIM
fwft_fifo 
#(
	.fifo_dw	(A_W+D_W+1),
	.fifo_depth	(FD+2*HR),
	.LOC		("w"),
	.HR		(HR)
)
r_fifo
(
	.clk		(clk				),
	.rst		(rst				),
	.d_in		(s_axis_r_wdata_hr[HR-1]	),//
	.wr_en		(s_axis_r_wvalid_hr[HR-1]	),//
	.full_early		(r_fifo_full			),//
	.d_out		(pi_i_d_r			),//
	.d_valid_out	(pi_i_v_r			),//
	.rd_en		(~pi_i_bp_r & ~r_fifo_empty	),//
	.empty		(r_fifo_empty			),//
	.done		(r_fifo_done			) //
);
`endif

`ifdef XLNXSRLFIFO

fifo_generator_1 r_fifo
(
	.clk		(clk				),
	.srst		(rst				),
	.din		({s_axis_r_wvalid,s_axis_r_wdata_hr[HR-1]}	),//
	.wr_en		(s_axis_r_wvalid_hr[HR-1]	),//
	.full		(r_fifo_full			),//
	.dout		({pi_i_v_r,pi_i_d_r}			),//
	.rd_en		(~pi_i_bp_r & ~r_fifo_empty	),//
	.empty		(r_fifo_empty			)//
//	.done		(r_fifo_done			) //
);
`endif

reg	[A_W+D_W:0]	s_axis_u0_wdata_hr	[HR-1:0];
reg			s_axis_u0_wvalid_hr	[HR-1:0];
reg			s_axis_u0_wready_hr	[HR-1:0];

wire	[A_W+D_W:0]	pi_o_d_u0;
wire			pi_o_v_u0;
wire			pi_o_b_u0;

assign	m_axis_u0_wdata	= pi_o_d_u0[A_W+D_W-1:0];
assign	m_axis_u0_wvalid= pi_o_v_u0;
assign	pi_o_b_u0	= ~m_axis_u0_wready;
assign	m_axis_u0_wlast	= pi_o_d_u0[A_W+D_W];

assign	s_axis_u0_wready= s_axis_u0_wready_hr[HR-1];

integer hr_u0;

always@(posedge clk)
begin
	s_axis_u0_wdata_hr[0]	<= {s_axis_u0_wlast,s_axis_u0_wdata};
	s_axis_u0_wvalid_hr[0]	<= s_axis_u0_wvalid;
	s_axis_u0_wready_hr[0]	<= ~u0_fifo_full;
	for(hr_u0=0;hr_u0<HR-1;hr_u0=hr_u0+1)
	begin
		s_axis_u0_wdata_hr[hr_u0+1]	<= s_axis_u0_wdata_hr[hr_u0];
		s_axis_u0_wvalid_hr[hr_u0+1]	<= s_axis_u0_wvalid_hr[hr_u0];
		s_axis_u0_wready_hr[hr_u0+1]	<= s_axis_u0_wready_hr[hr_u0];
	end

end


wire			u0_fifo_empty;
wire			u0_fifo_done;
wire			u0_fifo_full;

wire	[A_W+D_W:0]	pi_i_d_u0;
wire			pi_i_v_u0;
wire			pi_i_bp_u0;

`ifdef SIM
fwft_fifo 
#(
	.fifo_dw	(A_W+D_W+1),
	.fifo_depth	(FD+2*HR),
	.LOC		("w"),
	.HR		(HR)
)
u0_fifo
(
	.clk		(clk				),
	.rst		(rst				),
	.d_in		(s_axis_u0_wdata_hr[HR-1]	),//
	.wr_en		(s_axis_u0_wvalid_hr[HR-1]	),//
	.full_early		(u0_fifo_full			),//
	.d_out		(pi_i_d_u0			),//
	.d_valid_out	(pi_i_v_u0			),//
	.rd_en		(~pi_i_bp_u0 & ~u0_fifo_empty	),//
	.empty		(u0_fifo_empty			),//
	.done		(u0_fifo_done			) //
);
`endif

`ifdef XLNXSRLFIFO
fifo_generator_1 u0_fifo
(
	.clk		(clk				),
	.srst		(rst				),
	.din		({s_axis_u0_wvalid,s_axis_u0_wdata_hr[HR-1]}	),//
	.wr_en		(s_axis_u0_wvalid_hr[HR-1]	),//
	.full		(u0_fifo_full			),//
	.dout		({pi_i_v_u0,pi_i_d_u0}			),//
	.rd_en		(~pi_i_bp_u0 & ~u0_fifo_empty	),//
	.empty		(u0_fifo_empty			)//
);
`endif

reg	[A_W+D_W:0]	s_axis_u1_wdata_hr	[HR-1:0];
reg			s_axis_u1_wvalid_hr	[HR-1:0];
reg			s_axis_u1_wready_hr	[HR-1:0];


wire	[A_W+D_W:0]	pi_o_d_u1;
wire			pi_o_v_u1;
wire			pi_o_b_u1;

assign	m_axis_u1_wdata	= pi_o_d_u1[A_W+D_W-1:0];
assign	m_axis_u1_wvalid= pi_o_v_u1;
assign	pi_o_b_u1	= ~m_axis_u1_wready;
assign	m_axis_u1_wlast	= pi_o_d_u1[A_W+D_W];

assign	s_axis_u1_wready= s_axis_u1_wready_hr[HR-1];

integer hr_u1;

always@(posedge clk)
begin
	s_axis_u1_wdata_hr[0]	<= {s_axis_u1_wlast,s_axis_u1_wdata};
	s_axis_u1_wvalid_hr[0]	<= s_axis_u1_wvalid;
	s_axis_u1_wready_hr[0]	<= ~u1_fifo_full;
	for(hr_u1=0;hr_u1<HR-1;hr_u1=hr_u1+1)
	begin
		s_axis_u1_wdata_hr[hr_u1+1]		<= s_axis_u1_wdata_hr[hr_u1];
		s_axis_u1_wvalid_hr[hr_u1+1]	<= s_axis_u1_wvalid_hr[hr_u1];
		s_axis_u1_wready_hr[hr_u1+1]	<= s_axis_u1_wready_hr[hr_u1];
	end

end


wire			u1_fifo_empty;
wire			u1_fifo_done;
wire			u1_fifo_full;

wire	[A_W+D_W:0]	pi_i_d_u1;
wire			pi_i_v_u1;
wire			pi_i_bp_u1;

`ifdef SIM
fwft_fifo 
#(
	.fifo_dw	(A_W+D_W+1),
	.fifo_depth	(FD+2*HR),
	.LOC		("w"),
	.HR		(HR)
)
u1_fifo
(
	.clk		(clk				),
	.rst		(rst				),
	.d_in		(s_axis_u1_wdata_hr[HR-1]	),//
	.wr_en		(s_axis_u1_wvalid_hr[HR-1]	),//
	.full_early		(u1_fifo_full			),//
	.d_out		(pi_i_d_u1			),//
	.d_valid_out	(pi_i_v_u1			),//
	.rd_en		(~pi_i_bp_u1 & ~u1_fifo_empty	),//
	.empty		(u1_fifo_empty			),//
	.done		(u1_fifo_done			) //
);
`endif
`ifdef XLNXSRLFIFO
fifo_generator_1 u1_fifo
(
	.clk		(clk				),
	.srst		(rst				),
	.din		({s_axis_u1_wvalid,s_axis_u1_wdata_hr[HR-1]}	),//
	.wr_en		(s_axis_u1_wvalid_hr[HR-1]	),//
	.full		(u1_fifo_full			),//
	.dout		({pi_i_v_u1,pi_i_d_u1}			),//
	.rd_en		(~pi_i_bp_u1 & ~u1_fifo_empty	),//
	.empty		(u1_fifo_empty			)//
//	.done		(u1_fifo_done			) //
);
`endif

pi_switch
#(
	.N		(N	),	
	.WRAP		(WRAP	),
	.A_W		(A_W	),
	.D_W		(D_W	),
	.posl  		(posl	),
	.posx 		(posx	)
)
pi_switch_inst
(
	.clk		(clk		),		// clock
	.rst		(rst		),		// reset
	.ce		(ce		),		// clock enable
	`ifdef SIM
	.done		(done		),	// done
	`endif
	.l_i		(pi_i_d_l	),	// left  input payload
	.l_i_bp		(pi_i_bp_l	),	// left  input backpressured
	.l_i_v		(pi_i_v_l	),	// left  input valid
	.r_i		(pi_i_d_r	),	// right input payload
	.r_i_bp		(pi_i_bp_r	),	// right input backpressured
	.r_i_v		(pi_i_v_r	),	// right input valid
	.u0_i		(pi_i_d_u0	),	// u0    input payload
	.u0_i_bp	(pi_i_bp_u0	),	// u0    input backpressured
	.u0_i_v		(pi_i_v_u0	),	// u0    input valid
	.u1_i		(pi_i_d_u1	),	// u1    input payload
	.u1_i_bp	(pi_i_bp_u1	),	// u1    input backpressured
	.u1_i_v		(pi_i_v_u1	),	// u1    input valid
	.l_o		(pi_o_d_l	),	// left  output payload
	.l_o_bp		(pi_o_b_l	),	// left  output backpressured
	.l_o_v		(pi_o_v_l	),	// left  output valid
	.r_o		(pi_o_d_r	),	// right output payload
	.r_o_bp		(pi_o_b_r	),	// right output backpressured
	.r_o_v		(pi_o_v_r	),	// right output valid
	.u0_o		(pi_o_d_u0	),	// u0    output payload
	.u0_o_bp	(pi_o_b_u0	),	// u0    output backpressured
	.u0_o_v		(pi_o_v_u0	),	// u0    output valid
	.u1_o		(pi_o_d_u1	),	// u1    output payload
	.u1_o_bp	(pi_o_b_u1	),	// u1    output backpressured
	.u1_o_v		(pi_o_v_u1	)	// u1    output valid
);
`else
reg     [A_W+D_W-1:0]   previous_l;
reg     [A_W+D_W-1:0]   previous_r;
reg     [A_W+D_W-1:0]   previous_u0;
reg     [A_W+D_W-1:0]   previous_u1;
integer now=0;



always@(posedge clk)
begin
	now <= now+1;
    if (previous_l!=m_axis_l_wdata )//&& m_axis_l_wready==1'b11 && m_axis_l_wvalid==1'1b1)
    begin
        $display("Time%0d: switching",now-1);
        previous_l <= m_axis_l_wdata;
    end
    if (previous_r!=m_axis_r_wdata )//&& m_axis_l_wready==1'b11 && m_axis_l_wvalid==1'1b1)
    begin
        $display("Time%0d: switching",now-1);
        previous_r <= m_axis_r_wdata;
    end
    if (previous_u0!=m_axis_u0_wdata )//&& m_axis_l_wready==1'b11 && m_axis_l_wvalid==1'1b1)
    begin
        $display("Time%0d: switching",now-1);
        previous_u0 <= m_axis_u0_wdata;
    end
    if (previous_u1!=m_axis_u1_wdata )//&& m_axis_l_wready==1'b11 && m_axis_l_wvalid==1'1b1)
    begin
        $display("Time%0d: switching",now-1);
        previous_u1 <= m_axis_u1_wdata;
    end
end


wire	[A_W+D_W:0]	pi_o_d_l;
wire			pi_o_v_l;
wire			pi_o_b_l;

wire	[A_W+D_W:0]	pi_o_d_r;
wire			pi_o_v_r;
wire			pi_o_b_r;

wire	[A_W+D_W:0]	pi_o_d_u0;
wire			pi_o_v_u0;
wire			pi_o_b_u0;

wire	[A_W+D_W:0]	pi_o_d_u1;
wire			pi_o_v_u1;
wire			pi_o_b_u1;

assign	m_axis_l_wdata	= pi_o_d_l[A_W+D_W-1:0];
assign	m_axis_l_wvalid	= pi_o_v_l;
assign	pi_o_b_l	= ~m_axis_l_wready;
assign	m_axis_l_wlast	= pi_o_d_l[A_W+D_W];

assign	m_axis_r_wdata	= pi_o_d_r[A_W+D_W-1:0];
assign	m_axis_r_wvalid	= pi_o_v_r;
assign	pi_o_b_r	= ~m_axis_r_wready;
assign	m_axis_r_wlast	= pi_o_d_r[A_W+D_W];

assign	m_axis_u0_wdata	= pi_o_d_u0[A_W+D_W-1:0];
assign	m_axis_u0_wvalid= pi_o_v_u0;
assign	pi_o_b_u0	= ~m_axis_u0_wready;
assign	m_axis_u0_wlast	= pi_o_d_u0[A_W+D_W];

assign	m_axis_u1_wdata	= pi_o_d_u1[A_W+D_W-1:0];
assign	m_axis_u1_wvalid= pi_o_v_u1;
assign	pi_o_b_u1	= ~m_axis_u1_wready;
assign	m_axis_u1_wlast	= pi_o_d_u1[A_W+D_W];

wire	[A_W+D_W:0]	pi_i_d_l;
wire			pi_i_v_l;
wire			pi_i_b_l;

wire	[A_W+D_W:0]	pi_i_d_r;
wire			pi_i_v_r;
wire			pi_i_b_r;

wire	[A_W+D_W:0]	pi_i_d_u0;
wire			pi_i_v_u0;
wire			pi_i_b_u0;

wire	[A_W+D_W:0]	pi_i_d_u1;
wire			pi_i_v_u1;
wire			pi_i_b_u1;

pi_switch
#(
	.N		(N	),	
	.WRAP		(WRAP	),
	.A_W		(A_W	),
	.D_W		(D_W	),
	.posl  		(posl	),
	.posx 		(posx	)
)
pi_switch_inst
(
	.clk		(clk		),		// clock
	.rst		(rst		),		// reset
	.ce		(ce		),		// clock enable
	`ifdef SIM
	.done		(done		),	// done
	`endif
	.l_i		(pi_i_d_l	),	// left  input payload
	.l_i_bp		(pi_i_b_l	),	// left  input backpressured
	.l_i_v		(pi_i_v_l	),	// left  input valid
	.r_i		(pi_i_d_r	),	// right input payload
	.r_i_bp		(pi_i_b_r	),	// right input backpressured
	.r_i_v		(pi_i_v_r	),	// right input valid
	.u0_i		(pi_i_d_u0	),	// u0    input payload
	.u0_i_bp	(pi_i_b_u0	),	// u0    input backpressured
	.u0_i_v		(pi_i_v_u0	),	// u0    input valid
	.u1_i		(pi_i_d_u1	),	// u1    input payload
	.u1_i_bp	(pi_i_b_u1	),	// u1    input backpressured
	.u1_i_v		(pi_i_v_u1	),	// u1    input valid
	.l_o		(pi_o_d_l	),	// left  input payload
	.l_o_bp		(pi_o_b_l	),	// left  input backpressured
	.l_o_v		(pi_o_v_l	),	// left  input valid
	.r_o		(pi_o_d_r	),	// right input payload
	.r_o_bp		(pi_o_b_r	),	// right input backpressured
	.r_o_v		(pi_o_v_r	),	// right input valid
	.u0_o		(pi_o_d_u0	),	// u0    input payload
	.u0_o_bp	(pi_o_b_u0	),	// u0    input backpressured
	.u0_o_v		(pi_o_v_u0	),	// u0    input valid
	.u1_o		(pi_o_d_u1	),	// u1    input payload
	.u1_o_bp	(pi_o_b_u1	),	// u1    input backpressured
	.u1_o_v		(pi_o_v_u1	)	// u1    input valid
);

wire	[A_W+D_W:0]	bp_i_d_l;
wire			bp_i_v_l;
wire			bp_i_b_l;

wire	[A_W+D_W:0]	bp_o_d_l;
wire			bp_o_v_l;
wire			bp_o_b_l;


assign	bp_i_v_l	= s_axis_l_wvalid;
assign	bp_i_d_l	= {s_axis_l_wlast, s_axis_l_wdata};
assign	s_axis_l_wready	= ~bp_i_b_l;

assign	pi_i_v_l	= bp_o_v_l;
assign	pi_i_d_l	= bp_o_d_l;
assign	bp_o_b_l	= pi_i_b_l;

shadow_reg_combi
#(
	.D_W		(D_W	),
	.A_W		(A_W	)
)
bp_L
(
	.clk		(clk		), 
	.rst		(rst		), 
	.i_v		(bp_i_v_l	),
	.i_d		(bp_i_d_l	), 
 	.i_b		(bp_i_b_l	),
 	.o_v		(bp_o_v_l	),
	.o_d		(bp_o_d_l	),	 
	.o_b		(bp_o_b_l	) // unregistered from DOR logic
);

wire	[A_W+D_W:0]	bp_i_d_r;
wire			bp_i_v_r;
wire			bp_i_b_r;

wire	[A_W+D_W:0]	bp_o_d_r;
wire			bp_o_v_r;
wire			bp_o_b_r;


assign	bp_i_v_r	= s_axis_r_wvalid;
assign	bp_i_d_r	= {s_axis_r_wlast, s_axis_r_wdata};
assign	s_axis_r_wready	= ~bp_i_b_r;

assign	pi_i_v_r	= bp_o_v_r;
assign	pi_i_d_r	= bp_o_d_r;
assign	bp_o_b_r	= pi_i_b_r;

shadow_reg_combi
#(
	.D_W		(D_W	),
	.A_W		(A_W	)
)
bp_R
(
	.clk		(clk		), 
	.rst		(rst		), 
	.i_v		(bp_i_v_r	),
	.i_d		(bp_i_d_r	), 
 	.i_b		(bp_i_b_r	),
 	.o_v		(bp_o_v_r	),
	.o_d		(bp_o_d_r	),	 
	.o_b		(bp_o_b_r	) // unregistered from DOR logic
);

wire	[A_W+D_W:0]	bp_i_d_u0;
wire			bp_i_v_u0;
wire			bp_i_b_u0;

wire	[A_W+D_W:0]	bp_o_d_u0;
wire			bp_o_v_u0;
wire			bp_o_b_u0;


assign	bp_i_v_u0	= s_axis_u0_wvalid;
assign	bp_i_d_u0	= {s_axis_u0_wlast, s_axis_u0_wdata};
assign	s_axis_u0_wready= ~bp_i_b_u0;

assign	pi_i_v_u0	= bp_o_v_u0;
assign	pi_i_d_u0	= bp_o_d_u0;
assign	bp_o_b_u0	= pi_i_b_u0;

shadow_reg_combi
#(
	.D_W		(D_W	),
	.A_W		(A_W	)
)
bp_U0
(
	.clk		(clk		), 
	.rst		(rst		), 
	.i_v		(bp_i_v_u0	),
	.i_d		(bp_i_d_u0	), 
 	.i_b		(bp_i_b_u0	),
 	.o_v		(bp_o_v_u0	),
	.o_d		(bp_o_d_u0	),	 
	.o_b		(bp_o_b_u0	) // unregistered from DOR logic
);

wire	[A_W+D_W:0]	bp_i_d_u1;
wire			bp_i_v_u1;
wire			bp_i_b_u1;

wire	[A_W+D_W:0]	bp_o_d_u1;
wire			bp_o_v_u1;
wire			bp_o_b_u1;


assign	bp_i_v_u1	= s_axis_u1_wvalid;
assign	bp_i_d_u1	= {s_axis_u1_wlast, s_axis_u1_wdata};
assign	s_axis_u1_wready= ~bp_i_b_u1;

assign	pi_i_v_u1	= bp_o_v_u1;
assign	pi_i_d_u1	= bp_o_d_u1;
assign	bp_o_b_u1	= pi_i_b_u1;

shadow_reg_combi
#(
	.D_W		(D_W	),
	.A_W		(A_W	)
)
bp_U1
(
	.clk		(clk		), 
	.rst		(rst		), 
	.i_v		(bp_i_v_u1	),
	.i_d		(bp_i_d_u1	), 
 	.i_b		(bp_i_b_u1	),
 	.o_v		(bp_o_v_u1	),
	.o_d		(bp_o_d_u1	),	 
	.o_b		(bp_o_b_u1	) // unregistered from DOR logic
);
`endif
endmodule
