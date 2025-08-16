
`include	"commands.h"

module client_top 
#(
	parameter N 	= 2,		// total number of clients
	parameter D_W	= 32,		// data width
	parameter A_W	= $clog2(N)+1,	// address width
	parameter WRAP  = 1,            // wrapping means throttling of reinjection
	parameter PAT   = `RANDOM,      // default RANDOM pattern
	parameter RATE  = 10,           // rate of injection (in percent) 
	parameter LIMIT = 16,           // when to stop injectin packets
	parameter SIGMA = 4,            // radius for LOCAL traffic
	parameter posx 	= 2		// position
)
(
	input				clk,
	input				rst,
	input				ce,
	input		`Cmd		cmd,
	
	input		[A_W+D_W-1:0]	s_axis_c_wdata,
	input				s_axis_c_wvalid,
	output	wire			s_axis_c_wready,
	input				s_axis_c_wlast,

	output	wire	[A_W+D_W-1:0]	m_axis_c_wdata,
	output	wire			m_axis_c_wvalid,
	input				m_axis_c_wready,
	output	wire			m_axis_c_wlast,

	output	wire			done
);


`ifdef HYPERFLEX

wire lol;
assign	s_axis_c_wready	= ~lol;

client
#(
	.N		(N		), 	
	.D_W		(D_W		),
	.A_W		(A_W		),
	.WRAP		(WRAP		),	
	.PAT		(PAT		),
	.RATE  		(RATE		),
	.LIMIT		(LIMIT		),
	.SIGMA		(SIGMA		),
	.posx		(posx		)
)
client_inst
(
	.clk		(clk		),
	.rst		(rst		),
	.ce		(ce		),
	.cmd		(cmd		),
	
	.c_i		(s_axis_c_wdata	),
	.c_i_v		(s_axis_c_wvalid),
	.c_i_bp		(lol),

	.c_o		(m_axis_c_wdata	),
	.c_o_v		(m_axis_c_wvalid),
	.c_o_bp		(~m_axis_c_wready),

	.done		(done		)
);
`else	
wire	[A_W+D_W:0]	c_i_d_c;
wire			c_i_v_c;
wire			c_i_b_c;

wire	[A_W+D_W:0]	c_o_d_c;
wire			c_o_v_c;
wire			c_o_b_c;

wire			bp_i_v_c;
wire			bp_i_b_c;
wire	[A_W+D_W:0]	bp_i_d_c;

assign	bp_i_v_c	= s_axis_c_wvalid;
assign	bp_i_d_c	= {s_axis_c_wlast, s_axis_c_wdata};
assign	s_axis_c_wready	= ~bp_i_b_c;

wire			bp_o_v_c;
wire			bp_o_b_c;
wire	[A_W+D_W:0]	bp_o_d_c;

assign	c_i_d_c		= bp_o_d_c;
assign	c_i_v_c		= bp_o_v_c;
assign	bp_o_b_c	= c_i_b_c;

assign	m_axis_c_wdata	= c_o_d_c[A_W+D_W-1:0];
assign	m_axis_c_wvalid	= c_o_v_c;
assign	c_o_b_c		= ~m_axis_c_wready;
assign	m_axis_c_wlast	= c_o_d_c[A_W+D_W];

client
#(
	.N		(N		), 	
	.D_W		(D_W		),
	.A_W		(A_W		),
	.WRAP		(WRAP		),	
	.PAT		(PAT		),
	.RATE  		(RATE		),
	.LIMIT		(LIMIT		),
	.SIGMA		(SIGMA		),
	.posx		(posx		)
)
client_inst
(
	.clk		(clk		),
	.rst		(rst		),
	.ce		(ce		),
	.cmd		(cmd		),
	
	.c_i		(c_i_d_c	),
	.c_i_v		(c_i_v_c	),
	.c_i_bp		(c_i_b_c	),

	.c_o		(c_o_d_c	),
	.c_o_v		(c_o_v_c	),
	.c_o_bp		(c_o_b_c	),

	.done		(done		)
);

shadow_reg_combi
#(
	.D_W		(D_W	),
	.A_W		(A_W	)
)
bp_C
(
	.clk		(clk		), 
	.rst		(rst		), 
	.i_v		(bp_i_v_c	),
	.i_d		(bp_i_d_c	), 
	.i_b		(bp_i_b_c	),
	.o_v		(bp_o_v_c	),
	.o_d		(bp_o_d_c	), 
	.o_b		(bp_o_b_c	) 
);
`endif
endmodule
