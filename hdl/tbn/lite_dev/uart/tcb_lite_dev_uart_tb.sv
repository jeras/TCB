////////////////////////////////////////////////////////////////////////////////
// TCB-Lite UART testbench
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

module tcb_lite_dev_uart_tb
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

    // UART data width
    localparam int unsigned UART_DAT = 8;

    // UART baudrate
    localparam int unsigned TX_BDR = 4;         // TX baudrate
    localparam int unsigned RX_BDR = 4;         // RX baudrate
    localparam int unsigned RX_SMP = RX_BDR/2;  // RX sample

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

////////////////////////////////////////////////////////////////////////////////
// data checking
////////////////////////////////////////////////////////////////////////////////

    // UART signals
    logic uart_rxd;  // receive
    logic uart_txd;  // transmit

    // interrupts
    logic irq_tx;    // TX FIFO load is below limit
    logic irq_rx;    // RX FIFO load is above limit

    // TX string
    localparam string TX_STR = "Hello, World!";
    localparam int    TX_LEN = TX_STR.len();
    // RX string
    byte rx_str [TX_LEN];

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

        // write configuration
        $info("writing configuration begin.");
        man.write32('h08, DAT'(TX_BDR-1), sts, err);  // TX baudrate
        man.write32('h28, DAT'(RX_BDR-1), sts, err);  // RX baudrate
        man.write32('h2C, DAT'(RX_SMP-1), sts, err);  // RX sample
        man.write32('h30, DAT'(TX_LEN-1), sts, err);  // RX IRQ level
        $info("writing configuration end.");
        repeat (1) @(posedge clk);

        // read/check configuration
        $info("reading/checking configuration begin.");
        man.read32('h08, rdt, sts, err);  assert (rdt == 32'(TX_BDR-1)) else $error("TCB read mismatch");   // TX baudrate
        man.read32('h28, rdt, sts, err);  assert (rdt == 32'(RX_BDR-1)) else $error("TCB read mismatch");   // RX baudrate
        man.read32('h2C, rdt, sts, err);  assert (rdt == 32'(RX_SMP-1)) else $error("TCB read mismatch");   // RX sample
        man.read32('h30, rdt, sts, err);  assert (rdt == 32'(TX_LEN-1)) else $error("TCB read mismatch");   // RX IRQ level
        $info("reading/checking configuration end.");
        repeat (1) @(posedge clk);

        // write TX data
        $info("writing TX data begin.");
        for (int unsigned i=0; i<TX_LEN; i++) begin
            man.write32('h00, 32'(TX_STR[i]), sts, err);
        end
        $info("writing TX data end.");

        // wait for RX IRQ
        $info("writing RX IRQ begin.");
        do begin
            @(posedge clk);
        end while (!irq_rx);
        $info("writing RX IRQ end.");

        // read RX data
        $info("reading RX data begin.");
        for (int unsigned i=0; i<TX_LEN; i++) begin
            man.read32('h20, rdt, sts, err);
            rx_str[i] = rdt[UART_DAT-1:0];
        end
        $info("reading RX data end.");

        // checking if TX and RX data arrays are the same
        assert (string'(rx_str) == TX_STR) else
            $error("RX '%s' differs from TX '%s'", string'(rx_str), TX_STR);

        // end simulation
        repeat (4) @(posedge clk);
        $finish();
    end: test

    // timeout (in case RX IRQ is not triggered)
    initial
    begin
        repeat (TX_LEN*10*TX_BDR + 100) @(posedge clk);
        $error("ERROR: RX IRQ not triggered.");
        $finish();
    end

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

    // TCB UART
    tcb_lite_dev_uart #(
        .UART_DAT (UART_DAT)
    ) uart (
        // UART signals
        .uart_txd (uart_txd),
        .uart_rxd (uart_rxd),
        // interrupts
        .irq_tx   (irq_tx),
        .irq_rx   (irq_rx),
        // TCB interface
        .sub      (tcb_man)
    );

    // UART loopback
    assign uart_rxd = uart_txd;

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

endmodule: tcb_lite_dev_uart_tb
