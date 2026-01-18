////////////////////////////////////////////////////////////////////////////////
// TCB peripheral: UART controller
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

module tcb_peri_uart #(
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
    // system interface parameters
    localparam int unsigned SYS_ADR = 3,
    parameter  int unsigned SYS_DAT = 32,
    // TCB parameters
    parameter  bit          SYS_MIN = 1'b0   // minimalistic response implementation
)(
    // UART signals
    input  logic uart_rxd,  // receive
    output logic uart_txd,  // transmit
    // system signals
    input  logic               clk,  // clock
    input  logic               rst,  // reset
    // system bus write interface
    input  logic               sys_wen,  // write enable
    input  logic [SYS_ADR-1:0] sys_wad,  // write address
    input  logic [SYS_DAT-1:0] sys_wdt,  // write data
    // system bus read interface
    input  logic               sys_ren,  // read enable
    input  logic [SYS_ADR-1:0] sys_rad,  // read address
    output logic [SYS_DAT-1:0] sys_rdt,  // read data
    // interrupt request interface
    output logic               irq_tx,   // TX FIFO load is below limit
    output logic               irq_rx    // RX FIFO load is above limit
);

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // TX/RX baudrate signals
    logic [UART_RW-1:0] tx_cfg_bdr, rx_cfg_bdr;  //  baudrate time
    logic [UART_RW-1:0]             rx_cfg_smp;  //  sample time
    // TX/RX FIFO status
    logic [FIFO_CW-1:0] tx_sts_cnt, rx_sts_cnt;  // counter
    // TX/RX IRQ configuration
    logic [FIFO_CW-1:0] tx_cfg_irq, rx_cfg_irq;  // level

    // TX/RX FIFO stream (between TCB and FIFO)
    logic               tx_bus_vld, rx_bus_vld;  // valid
    logic [UART_DW-1:0] tx_bus_dat, rx_bus_dat;  // data
    logic               tx_bus_rdy, rx_bus_rdy;  // ready

    // TX/RX Ser/des stream (between FIFO and SER/DES)
    logic               tx_str_vld, rx_str_vld;  // valid
    logic [UART_DW-1:0] tx_str_dat, rx_str_dat;  // data
    logic               tx_str_rdy, rx_str_rdy;  // ready

////////////////////////////////////////////////////////////////////////////////
// TCB read access
////////////////////////////////////////////////////////////////////////////////

    // read configuration/status and RX data
    always_comb
    case (sys_rad)
        // TX channel
        4'h0: sys_rdt =           'x                       ;  // TX data
        4'h1: sys_rdt =                SYS_DAT'(tx_sts_cnt);  // TX FIFO load
        4'h2: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(tx_cfg_bdr);  // TX baudrate
        4'h3: sys_rdt =           'x                       ;  // TX reserved
        4'h4: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(tx_cfg_irq);  // TX interrupt trigger level
        // RX channel
        4'h8: sys_rdt =                SYS_DAT'(rx_bus_dat);  // RX data
        4'h9: sys_rdt =                SYS_DAT'(rx_sts_cnt);  // RX FIFO load
        4'ha: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(rx_cfg_bdr);  // RX baudrate
        4'hb: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(rx_cfg_smp);  // RX sample phase
        4'hc: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(rx_cfg_irq);  // RX interrupt trigger level
        // default
        default: sys_rdt =        'x;
    endcase

    // RX FIFO read side effect
    assign rx_bus_rdy = sys_ren & (sys_rad == 4'h8);

////////////////////////////////////////////////////////////////////////////////
// TCB write access
////////////////////////////////////////////////////////////////////////////////

    // write configuration and TX data
    always_ff @(posedge clk, posedge rst)
    if (rst) begin
        // TX channel
        tx_cfg_bdr <= CFG_TX_BDR_RST;
        tx_cfg_irq <= CFG_TX_IRQ_RST;
        // RX channel
        rx_cfg_bdr <= CFG_RX_BDR_RST;
        rx_cfg_smp <= CFG_RX_SMP_RST;
        rx_cfg_irq <= CFG_RX_IRQ_RST;
    end else if (sys_wen) begin
        if (sys_wen) begin
            // write access
            case (sys_wad)
                // TX channel
                4'h0:  /* write data goes directly into the TX FIFO      */ ;  // TX data
                4'h1:                                                       ;  // TX FIFO load
                4'h2: if (CFG_TX_BDR_WEN) tx_cfg_bdr <= sys_wdt[UART_RW-1:0];  // TX baudrate
                4'h3:                                                       ;  // TX reserved
                4'h4: if (CFG_TX_IRQ_WEN) tx_cfg_irq <= sys_wdt[FIFO_CW-1:0];  // TX interrupt trigger level
                // RX channel
                4'h8:                                                       ;  // RX data
                4'h9:                                                       ;  // RX FIFO load
                4'ha: if (CFG_RX_BDR_WEN) rx_cfg_bdr <= sys_wdt[UART_RW-1:0];  // RX baudrate
                4'hb: if (CFG_RX_SMP_WEN) rx_cfg_smp <= sys_wdt[UART_RW-1:0];  // RX sample phase
                4'hc: if (CFG_RX_IRQ_WEN) rx_cfg_irq <= sys_wdt[FIFO_CW-1:0];  // RX interrupt trigger level
                // default
                default: ;  // do nothing
            endcase
        end
    end

    // TX FIFO write side effect
    assign tx_bus_vld = sys_wen & sys_wen & (sys_wad == 4'h0);
    assign tx_bus_dat = sys_wdt[UART_DW-1:0];

////////////////////////////////////////////////////////////////////////////////
// TX channel
////////////////////////////////////////////////////////////////////////////////

    // FIFO
    tcb_peri_uart_fifo #(
        .SZ      (FIFO_SZ),
        .DW      (UART_DW)
    )  tx_fifo (
        // system signals
        .clk     (clk),
        .rst     (rst),
        // parallel stream input
        .sti_vld (tx_bus_vld),
        .sti_dat (tx_bus_dat),
        .sti_rdy (tx_bus_rdy),
        // parallel stream output
        .sto_vld (tx_str_vld),
        .sto_dat (tx_str_dat),
        .sto_rdy (tx_str_rdy),
        // status
        .cnt     (tx_sts_cnt)
    );

    // serializer
    tcb_peri_uart_ser #(
        .RW      (UART_RW),
        .DW      (UART_DW)
    ) tx_ser (
        // system signals
        .clk     (clk),
        .rst     (rst),
        // configuration
        .cfg_bdr (tx_cfg_bdr),
        // parallel stream
        .str_vld (tx_str_vld),
        .str_dat (tx_str_dat),
        .str_rdy (tx_str_rdy),
        // serial TX output
        .txd     (uart_txd)
    );

    // interrupt (TX FIFO load is below limit)
    assign irq_tx = (tx_sts_cnt < tx_cfg_irq);

////////////////////////////////////////////////////////////////////////////////
// RX channel
////////////////////////////////////////////////////////////////////////////////

    // FIFO
    tcb_peri_uart_fifo #(
        .SZ      (FIFO_SZ),
        .DW      (UART_DW)
    ) rx_fifo (
        // system signals
        .clk     (clk),
        .rst     (rst),
        // parallel stream input
        .sti_vld (rx_str_vld),
        .sti_dat (rx_str_dat),
        .sti_rdy (rx_str_rdy),
        // parallel stream output
        .sto_vld (rx_bus_vld),
        .sto_dat (rx_bus_dat),
        .sto_rdy (rx_bus_rdy),
        // status
        .cnt     (rx_sts_cnt)
    );

    // deserializer
    tcb_peri_uart_des #(
        .RW      (UART_RW),
        .DW      (UART_DW)
    ) rx_des (
        // system signals
        .clk     (clk),
        .rst     (rst),
        // configuration
        .cfg_bdr (rx_cfg_bdr),
        .cfg_smp (rx_cfg_smp),
        // parallel stream
        .str_vld (rx_str_vld),
        .str_dat (rx_str_dat),
        // serial RX input
        .rxd     (uart_rxd)
    );

    // interrupt (RX FIFO load is above limit)
    assign irq_rx = (rx_sts_cnt > rx_cfg_irq);

endmodule: tcb_peri_uart
