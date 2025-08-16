`include "system.h"

//`define UNIT_TEST_REACHABILITY2
//`define UNIT_TEST_REACHABILITY4
//`define UNIT_TEST_TRIANGLE_T
//`define UNIT_TEST_TRIANGLE_PI

`define UNIT_TEST_RND
//`define DEBUG
//`define DUMP 

// Testbench commands
`define Cmd [5:0]
`define Cmd_IDLE 6'd0
`define Cmd_01   6'd1
`define Cmd_02   6'd2
`define Cmd_03   6'd3
`define Cmd_10   6'd4
`define Cmd_12   6'd5
`define Cmd_13   6'd6
`define Cmd_20   6'd7
`define Cmd_21   6'd8
`define Cmd_23   6'd9
`define Cmd_30   6'd10
`define Cmd_31   6'd11
`define Cmd_32   6'd12
// deflection tests start here
`define Cmd_02_12     6'd13
`define Cmd_01_12     6'd14
`define Cmd_40_70     6'd15
`define Cmd_02_25     6'd16
`define Cmd_swap      6'd17
// randomized stress test
`define Cmd_RND       6'd18

`define RANDOM 0
`define LOCAL 1
`define BITREV 2
`define TORNADO 3
