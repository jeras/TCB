////////////////////////////////////////////////////////////////////////////////
// TCB-Lite interface peripheral: UART controller
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

module tcb_lite_peri_uart #(
    // UART parameters
    parameter  int unsigned UART_RW = 8,  // baudrate number width
    parameter  int unsigned UART_DW = 8,  // shifter data width
//    parameter string PARITY   = "NONE",         // parity type "EVEN", "ODD", "NONE"
//    parameter int    STOPSIZE = 1,              // number of stop bits
    // FIFO parameters
    parameter  int unsigned FIFO_SZ = 32,             // size
    localparam int unsigned FIFO_AW = $clog2(FIFO_SZ),     // address width
    localparam int unsigned FIFO_CW = $clog2(FIFO_SZ+1),   // counter width
    // configuration register parameters (write enable, reset value)
    parameter  bit CFG_TX_BDR_WEN = 1'b1, parameter  logic [UART_RW-1:0] CFG_TX_BDR_RST = '0,  // TX baudrate
    parameter  bit CFG_TX_IRQ_WEN = 1'b1, parameter  logic [FIFO_CW-1:0] CFG_TX_IRQ_RST = '0,  // TX interrupt level
    parameter  bit CFG_RX_BDR_WEN = 1'b1, parameter  logic [UART_RW-1:0] CFG_RX_BDR_RST = '0,  // RX baudrate
    parameter  bit CFG_RX_SMP_WEN = 1'b1, parameter  logic [UART_RW-1:0] CFG_RX_SMP_RST = '0,  // RX sample
    parameter  bit CFG_RX_IRQ_WEN = 1'b1, parameter  logic [FIFO_CW-1:0] CFG_RX_IRQ_RST = '0,  // RX interrupt level
    // TCB parameters
    parameter  bit          SYS_MIN = 1'b0   // minimalistic response implementation
)(
    // UART
    input  logic uart_rxd,  // receive
    output logic uart_txd,  // transmit
    // interrupts
    output logic irq_tx,    // TX FIFO load is below limit
    output logic irq_rx,    // RX FIFO load is above limit
    // TCB interface
    tcb_lite_if.sub sub
);

////////////////////////////////////////////////////////////////////////////////
// GPIO instance
////////////////////////////////////////////////////////////////////////////////

    logic [4-1:0] sys_req_adr;

    assign sys_req_adr = sub.req.adr[sub.MAX+:4];

    // TCB variant independent instance
    tcb_peri_uart #(
        // UART parameters
        .UART_RW  (UART_RW),
        .UART_DW  (UART_DW),
    //  .PARITY
    //  .STOPSIZE
        // FIFO parameters
        .FIFO_SZ  (FIFO_SZ),
        // configuration register parameters (write enable, reset value)
        .CFG_TX_BDR_WEN (CFG_TX_BDR_WEN),  .CFG_TX_BDR_RST (CFG_TX_BDR_RST),
        .CFG_TX_IRQ_WEN (CFG_TX_IRQ_WEN),  .CFG_TX_IRQ_RST (CFG_TX_IRQ_RST),
        .CFG_RX_BDR_WEN (CFG_RX_BDR_WEN),  .CFG_RX_BDR_RST (CFG_RX_BDR_RST),
        .CFG_RX_SMP_WEN (CFG_RX_SMP_WEN),  .CFG_RX_SMP_RST (CFG_RX_SMP_RST),
        .CFG_RX_IRQ_WEN (CFG_RX_IRQ_WEN),  .CFG_RX_IRQ_RST (CFG_RX_IRQ_RST),
        // system interface parameters
        .SYS_DAT  (sub.DAT),
        // TCB parameters
        .SYS_MIN  (SYS_MIN)
    ) uart (
        // UART signals
        .uart_rxd (uart_rxd),
        .uart_txd (uart_txd),
        // system signals
        .clk      (sub.clk),
        .rst      (sub.rst),
        // system write interface
        .sys_wen  (sub.req.wen & sub.trn),
        .sys_wad  (sys_req_adr),
        .sys_wdt  (sub.req.wdt),
        // system read interface
        .sys_ren  (~sub.req.wen & sub.trn),
        .sys_rad  (sys_req_adr),
        .sys_rdt  (sub.rsp.rdt),
        // interrupt request interface
        .irq_tx   (irq_tx),
        .irq_rx   (irq_rx)
    );

    // TCB status response
    assign sub.rsp.sts =   '0;
    assign sub.rsp.err = 1'b0;

    // TCB backpressure
    assign sub.rdy = 1'b1;

endmodule: tcb_lite_peri_uart
