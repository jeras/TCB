////////////////////////////////////////////////////////////////////////////////
// TCB UART testbench
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

module tcb_peri_uart_tb
    import tcb_pkg::*;
    import tcb_vip_blocking_pkg::*;
#(
    // TCB widths
    int unsigned ADR = 32,
    int unsigned DAT = 32
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

    // UART data width
    localparam int unsigned UDW = 8;

    // UART baudrate
    localparam int unsigned TX_BDR = 4;         // TX baudrate
    localparam int unsigned RX_BDR = 4;         // RX baudrate
    localparam int unsigned RX_SMP = RX_BDR/2;  // RX sample

    // configuration parameter
    localparam tcb_cfg_t CFG = '{
        // handshake parameter
        HSK: '{
            DLY: 0,
            HLD: 1'b0
        },
        // bus parameter
        BUS: '{
            ADR: TCB_BUS_DEF.ADR,
            DAT: TCB_BUS_DEF.DAT,
            LEN: TCB_BUS_DEF.LEN,
            LCK: TCB_LCK_PRESENT,
            CHN: TCB_CHN_HALF_DUPLEX,
            AMO: TCB_AMO_ABSENT,
            PRF: TCB_PRF_ABSENT,
            NXT: TCB_NXT_ABSENT,
            MOD: TCB_MOD_LOG_SIZE,
            ORD: TCB_ORD_DESCENDING,
            NDN: TCB_NDN_BI_NDN
        },
        // physical interface parameter
        PMA: TCB_PMA_DEF
    };

    localparam tcb_vip_t VIP = '{
        DRV: 1'b1
    };

//    typedef tcb_c #(HSK, BUS_SIZ, PMA)::req_t req_t;
//    typedef tcb_c #(HSK, BUS_SIZ, PMA)::rsp_t rsp_t;

    // local request/response types are copies of packaged defaults
    typedef tcb_req_t req_t;
    typedef tcb_rsp_t rsp_t;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // system signals (initialized)
    logic clk = 1'b1;  // clock
    logic rst = 1'b1;  // reset

    string testname = "none";

    // TCB interfaces
    tcb_if #(tcb_cfg_t, CFG, req_t, rsp_t) tcb_man (.clk (clk), .rst (rst));

    // parameterized class specialization (blocking API)
    typedef tcb_vip_blocking_c #(tcb_cfg_t, CFG, req_t, rsp_t) tcb_man_s;

    // TCB class objects
    tcb_man_s obj_man = new(tcb_man, "MAN");

    // response
    logic [tcb_man.CFG_BUS_BYT-1:0][8-1:0] rdt;  // read data
    tcb_rsp_sts_t                          sts;  // status response

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
        $display("(%t) INFO: writing configuration begin.", $time);
        obj_man.write32('h08, 32'(TX_BDR-1), sts);  // TX baudrate
        obj_man.write32('h28, 32'(RX_BDR-1), sts);  // RX baudrate
        obj_man.write32('h2C, 32'(RX_SMP-1), sts);  // RX sample
        obj_man.write32('h30, 32'(TX_LEN-1), sts);  // RX IRQ level
        $display("(%t) INFO: writing configuration end.", $time);
        repeat (1) @(posedge clk);

        // read/check configuration
        $display("(%t) INFO: reading/checking configuration begin.", $time);
        obj_man.check32('h08, 32'(TX_BDR-1), '0);  // TX baudrate
        obj_man.check32('h28, 32'(RX_BDR-1), '0);  // RX baudrate
        obj_man.check32('h2C, 32'(RX_SMP-1), '0);  // RX sample
        obj_man.check32('h30, 32'(TX_LEN-1), '0);  // RX IRQ level
        $display("(%t) INFO: reading/checking configuration end.", $time);
        repeat (1) @(posedge clk);

        // write TX data
        $display("(%t) INFO: writing TX data begin.", $time);
        for (int unsigned i=0; i<TX_LEN; i++) begin
            obj_man.write32('h00, 32'(TX_STR[i]), sts);
        end
        $display("(%t) INFO: writing TX data end.", $time);

        // wait for RX IRQ
        $display("(%t) INFO: writing RX IRQ begin.", $time);
        do begin
            @(posedge clk);
        end while (!irq_rx);
        $display("(%t) INFO: writing RX IRQ end.", $time);

        // read RX data
        $display("(%t) INFO: reading RX data begin.", $time);
        for (int unsigned i=0; i<TX_LEN; i++) begin
            obj_man.read32('h20, rdt, sts);
            rx_str[i] = rdt[UDW-1:0];
        end
        $display("(%t) INFO: reading RX data end.", $time);

        // checking if TX and RX data arrays are the same
        if (string'(rx_str) != TX_STR) begin
            $display("ERROR: RX '%s' differs from TX '%s'", string'(rx_str), TX_STR);
            $display("FAILURE");
        end else begin
            $display("SUCCESS");
        end

        // end simulation
        repeat (4) @(posedge clk);
        $finish();
    end: test

    // timeout (in case RX IRQ is not triggered)
    initial
    begin
        repeat (TX_LEN*10*TX_BDR + 100) @(posedge clk);
        $display("ERROR: RX IRQ not triggered.");
        $display("FAILURE");
        $finish();
    end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

    tcb_vip_protocol_checker chk_man (
        .tcb (tcb_man)
    );

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

    // TCB UART
    tcb_peri_uart #(
        .DW       (UDW)
    ) uart (
        // UART signals
        .uart_txd (uart_txd),
        .uart_rxd (uart_rxd),
        // interrupts
        .irq_tx   (irq_tx),
        .irq_rx   (irq_rx),
        // TCB interface
        .tcb      (tcb_man)
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

endmodule: tcb_peri_uart_tb
