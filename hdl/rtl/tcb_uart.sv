////////////////////////////////////////////////////////////////////////////////
// TCB interface UART controller
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

module tcb_uart #(
  // UART parameters
  int unsigned CW = 8,  // baudrate counter width
  int unsigned DW = 8,  // shifter data width
//  parameter string PARITY   = "NONE",         // parity type "EVEN", "ODD", "NONE"
//  parameter int    STOPSIZE = 1,              // number of stop bits
  // TX channel
  logic [CW-1:0] CFG_TXD_BDR_RST = '0,  logic CFG_TXD_BDR_ENA = 1'b1,
  logic [CW-1:0] CFG_TXD_IRQ_RST = '0,  logic CFG_TXD_IRQ_ENA = 1'b1,
  // RX channel
  logic [CW-1:0] CFG_RXD_BDR_RST = '0,  logic CFG_RXD_BDR_ENA = 1'b1,
  logic [CW-1:0] CFG_RXD_SMP_RST = '0,  logic CFG_RXD_SMP_ENA = 1'b1,
  logic [CW-1:0] CFG_RXD_IRQ_RST = '0,  logic CFG_RXD_IRQ_ENA = 1'b1
)(
  // UART
  input  logic uart_rxd,  // receive
  output logic uart_txd,  // transmit
  // system bus interface
  tcb_if.sub   bus
);

  // FIFO parameters
  localparam int unsigned SZ = 32;  // size
  localparam int unsigned AW =  6;  // address width

  // TX/RX baudrate signals
  logic [CW-1:0] tx_cfg_bdr, rx_cfg_bdr;  //  baudrate time
  logic [CW-1:0]             rx_cfg_smp;  //  sample time
  // TX/RX FIFO status
  logic [AW-1:0] tx_sts_cnt, rx_sts_cnt;  // counter
  // TX/RX IRQ configuration
  logic [AW-1:0] tx_cfg_irq, rx_cfg_irq;  // counter

  // TX/RX FIFO stream (between TCB and FIFO)
  logic          tx_bus_vld, rx_bus_vld;  // valid
  logic [DW-1:0] tx_bus_dat, rx_bus_dat;  // data
  logic          tx_bus_rdy, rx_bus_rdy;  // ready

  // TX/RX Ser/des stream (between FIFO and SER/DES)
  logic          tx_str_vld, rx_str_vld;  // valid
  logic [DW-1:0] tx_str_dat, rx_str_dat;  // data
  logic          tx_str_rdy, rx_str_rdy;  // ready

////////////////////////////////////////////////////////////////////////////////
// TCB access
////////////////////////////////////////////////////////////////////////////////

  // read configuration/status and RX data
  always_ff @(posedge bus.clk, posedge bus.rst)
  if (bus.rst) begin
    bus.rdt <= '0;
  end else if (bus.trn) begin
    if (~bus.wen) begin
      // read access
      case (bus.adr[6-1:0])
        // TX channel
        6'h00:   bus.rdt <= 'x;
        6'h04:   bus.rdt <= tx_sts_cnt;
        6'h08:   bus.rdt <= tx_cfg_bdr;
        6'h0C:   bus.rdt <= 'x;
        6'h10:   bus.rdt <= tx_cfg_irq;
        // RX channel
        6'h20:   bus.rdt <= rx_bus_dat;
        6'h24:   bus.rdt <= rx_sts_cnt;
        6'h28:   bus.rdt <= rx_cfg_bdr;
        6'h2C:   bus.rdt <= rx_cfg_smp;
        6'h30:   bus.rdt <= rx_cfg_irq;
        // default
        default: bus.rdt <= 'x;
      endcase
    end
  end

  // write configuration and TX data
  always_ff @(posedge bus.clk, posedge bus.rst)
  if (bus.rst) begin
    // TX channel
    tx_cfg_bdr <= CFG_TXD_BDR_RST;
    tx_cfg_irq <= CFG_TXD_IRQ_RST;
    // RX channel
    rx_cfg_bdr <= CFG_RXD_BDR_RST;
    rx_cfg_smp <= CFG_RXD_SMP_RST;
    rx_cfg_irq <= CFG_RXD_IRQ_RST;
  end else if (bus.trn) begin
    if (bus.wen) begin
      // write access
      case (bus.adr[4-1:0])
        // TX channel
        6'h00:   ;  // write data goes directly into the TX FIFO
        6'h04:   ;
        6'h08:   if (CFG_TXD_BDR_ENA) tx_cfg_bdr <= bus.wdt;
        6'h0C:   ;
        6'h10:   if (CFG_TXD_IRQ_ENA) tx_cfg_irq <= bus.wdt;
        // RX channel
        6'h20:   ;
        6'h24:   ;
        6'h28:   if (CFG_RXD_BDR_ENA) rx_cfg_bdr <= bus.rdt;
        6'h2C:   if (CFG_RXD_SMP_ENA) rx_cfg_smp <= bus.wdt;
        6'h30:   if (CFG_RXD_IRQ_ENA) rx_cfg_irq <= bus.rdt;
        // default
        default: ;  // do nothing
      endcase
    end
  end

  // controller response is immediate
  assign bus.rdy = 1'b1;

  // there are no error cases
  assign bus.err = 1'b0;

////////////////////////////////////////////////////////////////////////////////
// TX channel
////////////////////////////////////////////////////////////////////////////////

  assign tx_bus_vld = bus.trn & bus.wen & (bus.adr[6-1:0] == 6'h00);
  assign tx_bus_dat = bus.wdt;

  // FIFO
  tcb_uart_fifo #(
    .SZ      (SZ),
    .AW      (AW),
  //.CW      (8),
    .DW      (DW)
  ) tx_fifo (
    // system signals
    .clk     (bus.clk),
    .rst     (bus.rst),
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
  tcb_uart_ser #(
    .CW      (CW),
    .DW      (DW)
  ) tx_ser (
    // system signals
    .clk     (bus.clk),
    .rst     (bus.rst),
    // configuration
    .cfg_bdr (tx_cfg_bdr),
    // parallel stream
    .str_vld (tx_str_vld),
    .str_dat (tx_str_dat),
    .str_rdy (tx_str_rdy),
    // serial TX output
    .txd     (uart_txd)
  );

  // interrupt
//  assign irq_tx = 

////////////////////////////////////////////////////////////////////////////////
// RX channel
////////////////////////////////////////////////////////////////////////////////

  // FIFO
  tcb_uart_fifo #(
    .SZ      (SZ),
    .AW      (AW),
  //.CW      (8),
    .DW      (DW)
  ) rx_fifo (
    // system signals
    .clk     (bus.clk),
    .rst     (bus.rst),
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
  tcb_uart_des #(
    .CW      (CW),
    .DW      (DW)
  ) rx_des (
    // system signals
    .clk     (bus.clk),
    .rst     (bus.rst),
    // configuration
    .cfg_bdr (rx_cfg_bdr),
    .cfg_smp (rx_cfg_smp),
    // parallel stream
    .str_vld (rx_str_vld),
    .str_dat (rx_str_dat),
    // serial RX input
    .rxd     (uart_rxd)
  );

endmodule: tcb_uart