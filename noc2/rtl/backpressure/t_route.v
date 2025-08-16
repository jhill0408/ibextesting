/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off UNUSEDSIGNAL */
`include "mux.h"

module t_route #(
	parameter N	= 8,		// number of clients
	parameter A_W	= $clog2(N)+1,	// log number of clients
	parameter D_W	= 32,
	parameter posl  = 0,		// which level
	parameter posx 	= 0		// which position
) (
	input  	wire 			clk		,	// clock
	input  	wire 			rst		,	// reset
	input  	wire 			ce		,	// clock enable
	input  	wire 			l_i_v		,	// left input valid
	input  	wire 			r_i_v		,	// right input valid
	input  	wire 			u0_i_v		,	// up0 input valid
	output  wire 			l_i_bp		,	// left input is backpressured
	output  wire 			r_i_bp		,	// right input is backpressured
	output  wire 			u0_i_bp		,	// up0 input is backpressured
	input  	wire	[A_W-1:0]	l_i_addr	,	// left input addr
	input  	wire	[A_W-1:0] 	r_i_addr	,	// right input addr
	input  	wire 	[A_W-1:0] 	u0_i_addr	, 	// up0 input addr
	input  	wire	[D_W-1:0]	l_i_data	,	// left input addr
	input  	wire	[D_W-1:0] 	r_i_data	,	// right input addr
	input  	wire 	[D_W-1:0] 	u0_i_data	, 	// up0 input addr
	output 	wire			l_o_v		,	// valid for l mux
	output 	wire			r_o_v		,	// valid for r mux
	output 	wire			u0_o_v		,	// valid for u0 mux
	input	wire			l_o_bp		,	// left output is backpressured
	input	wire			r_o_bp		,	// right output is backpressured
	input	wire			u0_o_bp		,	// up0 output is backpressured
	output 	reg	     		l_sel		,	// select for l mux
	output 	reg	     		r_sel		,	// select for r mux
	output 	reg	     		u0_sel			// select for u0 mux
);

wire		l_wins, l_wants_r, l_wants_u0, l_gets_r, l_gets_u0;
wire 		r_wins, r_wants_l, r_wants_u0, r_gets_l, r_gets_u0;
wire 		u0_wins, u0_wants_l, u0_wants_r, u0_gets_l, u0_gets_r;

reg	[1:0]	rr; //0->L, 1->R,2->U0,3->U1

always@(posedge clk)
begin
	if(rst)
	begin
		rr	<= 0;
	end
	else
	begin
		case(rr)
			0:
			begin
				if(r_i_bp)
				begin
					rr	<= 1;
				end
				else if(u0_i_bp)
				begin
					rr	<= 2;
				end
			end
			1:
			begin
				if(u0_i_bp)
				begin
					rr	<= 2;
				end
				else if(l_i_bp)
				begin
					rr	<= 0;
				end
			end
			2:
			begin
				if(l_i_bp)
				begin
					rr	<= 0;
				end
				else if(r_i_bp)
				begin
					rr	<= 1;
				end
			end
            default:
            begin
                rr  <= 0;
            end
		endcase
	end
end


always@*
begin
	case({r_gets_l, u0_gets_l})
		2'b10:
		begin
			l_sel	= 1'b0;//`RIGHT -3'b001;
		end
		2'b01:
		begin
			l_sel	= 1'b1;//`U0 -3'b001;
		end
		default:
		begin
			l_sel	= 1'b0;
		end

	endcase
end

always@*
begin
	case({l_gets_r, u0_gets_r})
		2'b10:
		begin
			r_sel	= 1'b0;//`LEFT;
		end
		2'b01:
		begin
			r_sel	= 1'b1;//`U0-3'b001;			
		end
		default:
		begin
			r_sel	= 1'b0;
		end

	endcase
end

always@*
begin
	case({l_gets_u0, r_gets_u0})
		2'b10:
		begin
			u0_sel	= 1'b0;
		end
        2'b01:
        begin
            u0_sel  = 1'b1;
        end
		default:
		begin
			u0_sel	= 1'b0;
		end

	endcase
end

assign	l_wins	= ( (rr==0) );//| (rr==2 & ~u0_wants_r) | (rr==1 & ~r_wants_u0) ) ;
assign	r_wins	= ( (rr==1) );//| (rr==2 & ~u0_wants_l) | (rr==0 & ~l_wants_u0) ) ;
assign	u0_wins	= ( (rr==2) );//| (rr==0 & ~l_wants_r)  | (rr==1 & ~r_wants_l)  ) ;

assign l_wants_r 	= l_i_v & l_i_addr[posl] & l_i_addr[A_W-1:posl+1]==posx[A_W-1:posl];
assign l_wants_u0 	= l_i_v & l_i_addr[A_W-1:posl+1]!=posx[A_W-1:posl];// & l_i_addr[posl] ;

assign r_wants_l 	= r_i_v & ~r_i_addr[posl] & r_i_addr[A_W-1:posl+1]==posx[A_W-1:posl];
assign r_wants_u0 	= r_i_v & r_i_addr[A_W-1:posl+1]!=posx[A_W-1:posl];// & ~r_i_addr[posl];
	
assign u0_wants_l 	= u0_i_v & ~u0_i_addr[posl];
assign u0_wants_r 	= u0_i_v & u0_i_addr[posl];
	
assign	l_gets_r	= 	(~r_o_bp) & (l_wants_r)  & ( (l_wins)  | (~u0_wants_r) );
assign	u0_gets_r	= 	(~r_o_bp) & (u0_wants_r) & ( (u0_wins) | (~l_wants_r ) );
				
assign	r_gets_l	= 	(~l_o_bp) & (r_wants_l)  & ( (r_wins)  | (~u0_wants_l) );
assign	u0_gets_l	= 	(~l_o_bp) & (u0_wants_l) & ( (u0_wins) | (~r_wants_l ) );

assign	l_gets_u0	= 	(~u0_o_bp) & (l_wants_u0) & ( (l_wins) | (~r_wants_u0) ) ;
assign	r_gets_u0	= 	(~u0_o_bp) & (r_wants_u0) & ( (r_wins) | (~l_wants_u0) ) ;


assign	l_i_bp		=	(l_wants_r  & ~l_gets_r)  | (l_wants_u0 & ~l_gets_u0) ;
assign	r_i_bp		=	(r_wants_l  & ~r_gets_l)  | (r_wants_u0 & ~r_gets_u0);
assign	u0_i_bp		=	(u0_wants_l & ~u0_gets_l) | (u0_wants_r & ~u0_gets_r) ;

assign	l_o_v		=	r_gets_l  | u0_gets_l ;
assign	r_o_v		=	l_gets_r  | u0_gets_r ;
assign	u0_o_v		=	l_gets_u0 | r_gets_u0 ;

endmodule
