////////////////////////////////////////////////////////////////////////////////
// TCB-Lite GPIO testbench
////////////////////////////////////////////////////////////////////////////////
// Copyright 2022 Iztok Jeras
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
////////////////////////////////////////////////////////////////////////////////

module tcb_lite_peri_gpio_tb
    import tcb_lite_pkg::*;
#(
    // RTL configuration parameters
    parameter  int unsigned DLY =    0,  // response delay
    parameter  bit          HLD = 1'b0,  // response hold
    parameter  bit          MOD = 1'b0,  // bus mode (0-logarithmic size, 1-byte enable)
    parameter  int unsigned CTL =    0,  // control width (user defined request signals)
    parameter  int unsigned ADR =   32,  // address width (only 32/64 are supported)
    parameter  int unsigned DAT =   32,  // data    width (only 32/64 are supported)
    parameter  int unsigned STS =    0   // status  width (user defined response signals)
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

    // GPIO width
    localparam int unsigned GDW = 32;

    // TCB configurations               '{HSK: '{DLY, HLD}, BUS: '{MOD, CTL, ADR, DAT, STS}}
    localparam tcb_lite_cfg_t MAN_CFG = '{HSK: '{DLY, HLD}, BUS: '{MOD, CTL, ADR, DAT, STS}};

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // system signals (initialized)
    logic clk = 1'b1;  // clock
    logic rst = 1'b1;  // reset

    string testname = "none";

    // TCB interfaces
    tcb_lite_if #(MAN_CFG) tcb_man (.clk (clk), .rst (rst));

    // response
    logic [DAT-1:0] rdt;  // read data
    logic [STS-1:0] sts;  // response status
    logic           err;  // response error

    // interrupt
    logic           irq;

////////////////////////////////////////////////////////////////////////////////
// data checking
////////////////////////////////////////////////////////////////////////////////

    // GPIO signals
    logic [GDW-1:0] gpio_o;
    logic [GDW-1:0] gpio_e;
    logic [GDW-1:0] gpio_i;

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

    // clock
    always #(20ns/2) clk = ~clk;

    // test sequence
    initial
    begin: test
        // time dispaly formatting
        $timeformat(-9, 3, "ns", 12);
        // reset sequence
        repeat (2) @(posedge clk);
        rst <= 1'b0;
        repeat (1) @(posedge clk);

        // write configuration (output and enable registers)
        $info("writing configuration begin.");
        man.write32('h04, 32'h01234567, sts, err);  // write output data register
        man.write32('h00, 32'h76543210, sts, err);  // write output enable register
        $info("writing configuration end.");
        repeat (1) @(posedge clk);

        // check configuration (output and enable registers)
        $info("reading/checking configuration begin.");
        man.read32('h04, rdt, sts, err);  assert (rdt == 32'h01234567) else $error("TCB read mismatch");  // read output data register
        man.read32('h00, rdt, sts, err);  assert (rdt == 32'h76543210) else $error("TCB read mismatch");  // read output enable register
        $info("reading/checking configuration end.");
        repeat (1) @(posedge clk);

        // read/check GPIO input status
        man.write32('h08, 32'hffffffff, sts, err);  // write input enable register
        repeat (1) @(posedge clk);
        $info("reading/checking input begin.");
        #10ns gpio_i = GDW'('h89abcdef);
        repeat (2) @(posedge clk);
        man.read32('h0c, rdt, sts, err);  assert (rdt == 32'h89abcdef) else $error("TCB read mismatch");  // read input data register
        #10ns gpio_i = GDW'('hfedcba98);
        repeat (2) @(posedge clk);
        man.read32('h0c, rdt, sts, err);  assert (rdt == 32'hfedcba98) else $error("TCB read mismatch");  // read input data register
        $info("reading/checking input end.");

        // TODO: interrupt support

        // end simulation
        repeat (4) @(posedge clk);
        $finish();
    end: test

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

    // manager VIP
    tcb_lite_vip_manager #(
    ) man (
        .man (tcb_man)
    );

    tcb_lite_vip_protocol_checker chk_man (
        .mon (tcb_man)
    );

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

    // TCB GPIO
    tcb_lite_peri_gpio #(
        .GDW     (GDW),
        // implementation details
//        bit          CFG_MIN = 1'b0,  // minimalistic implementation
        .CDC     (2)
    ) gpio (
        // GPIO signals
        .gpio_o  (gpio_o),
        .gpio_e  (gpio_e),
        .gpio_i  (gpio_i),
        // TCB interface
        .sub     (tcb_man),
        // IRQ interface
        .irq     (irq)
    );

//    // GPIO three state drivers and loopback
//    generate
//    for (genvar i=0; i<GDW; i++) begin: io
//        assign gpio_i[i] = gpio_e[i] ? gpio_o[i] : 'z;
//    end: io
//    endgenerate
    
////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

    initial
    begin
`ifdef VERILATOR
        $dumpfile("test.fst");
`else
        $dumpfile("test.vcd");
`endif
        $dumpvars;
    end

endmodule: tcb_lite_peri_gpio_tb
