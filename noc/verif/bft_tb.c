#include "Vbft.h"
#include "verilated.h"
#include <iostream>
//#include <verilated_vcd_c.h>
using namespace std;


int main(int argc, char **argv, char **env) {
        Verilated::commandArgs(argc, argv);
//	Verilated::traceEverOn(true);
//        VerilatedVcdC* tfp = new VerilatedVcdC;
	Vbft* top = new Vbft;
//	top->trace(tfp,99);
//	tfp->open("dump.vcd");
        // TODO: add initialization stuff for generics and add a clock loop
        int time=0;
        bool clk=0;
        top->ce = 1;
        top->rst = 1;
        top->clk = 0;
        top->in = 0;
	top->cmd = 18; // Cmd_RND=18 
        while (!Verilated::gotFinish() && !(top->done_all==1)) {
                top->rst = (time<2);
                top->clk = clk;
                top->eval();
                clk=!clk;
                time++;
//		tfp->dump (time);
        }
//      cout << "// Verilator simulation finished at time=" << time << endl;
//
//	tfp->close();
        delete top;
        exit(0);
}
