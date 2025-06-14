////////////////////////////////////////////////////////////////////////////////
// TCB interface (independent RW channels): UART controller
////////////////////////////////////////////////////////////////////////////////
// Copyright 2023 Iztok Jeras
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

module tcb_ind_uart #(
  // UART parameters
  int unsigned RW = 8,  // baudrate number width
  int unsigned DW = 8,  // shifter data width
//  parameter string PARITY   = "NONE",         // parity type "EVEN", "ODD", "NONE"
//  parameter int    STOPSIZE = 1,              // number of stop bits
  // FIFO parameters
  int unsigned SZ = 32,             // size
  int unsigned AW = $clog2(SZ),     // address width
  int unsigned CW = $clog2(SZ+1),   // counter width
  // configuration register parameters (write enable, reset value)
  bit   CFG_TX_BDR_WEN = 1'b1,  logic [RW-1:0] CFG_TX_BDR_RST = '0,  // TX baudrate
  bit   CFG_TX_IRQ_WEN = 1'b1,  logic [CW-1:0] CFG_TX_IRQ_RST = '0,  // TX interrupt level
  bit   CFG_RX_BDR_WEN = 1'b1,  logic [RW-1:0] CFG_RX_BDR_RST = '0,  // RX baudrate
  bit   CFG_RX_SMP_WEN = 1'b1,  logic [RW-1:0] CFG_RX_SMP_RST = '0,  // RX sample
  bit   CFG_RX_IRQ_WEN = 1'b1,  logic [CW-1:0] CFG_RX_IRQ_RST = '0,  // RX interrupt level
  // TCB parameters
  bit   CFG_RSP_REG = 1'b1,  // register response path (by default the response is registered giving a CFG.HSK.DLY of 1)
  bit   CFG_RSP_MIN = 1'b0   // minimalistic response implementation
)(
  // UART
  input  logic uart_rxd,  // receive
  output logic uart_txd,  // transmit
  // interrupts
  output logic irq_tx,    // TX FIFO load is below limit
  output logic irq_rx,    // RX FIFO load is above limit
  // TCB IRW interface
  tcb_if.sub tcb_rdc,
  tcb_if.sub tcb_wrc
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
generate
  if (tcb_rdc.HSK.DLY != 0)  $error("ERROR: %m parameter tcb_rdc.HSK.DLY validation failed");
  if (tcb_wrc.HSK.DLY != 0)  $error("ERROR: %m parameter tcb_wrc.HSK.DLY validation failed");
endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // TX/RX baudrate signals
  logic [RW-1:0] tx_cfg_bdr, rx_cfg_bdr;  //  baudrate time
  logic [RW-1:0]             rx_cfg_smp;  //  sample time
  // TX/RX FIFO status
  logic [CW-1:0] tx_sts_cnt, rx_sts_cnt;  // counter
  // TX/RX IRQ configuration
  logic [CW-1:0] tx_cfg_irq, rx_cfg_irq;  // level

  // TX/RX FIFO stream (between TCB and FIFO)
  logic          tx_bus_vld, rx_bus_vld;  // valid
  logic [DW-1:0] tx_bus_dat, rx_bus_dat;  // data
  logic          tx_bus_rdy, rx_bus_rdy;  // ready

  // TX/RX Ser/des stream (between FIFO and SER/DES)
  logic          tx_str_vld, rx_str_vld;  // valid
  logic [DW-1:0] tx_str_dat, rx_str_dat;  // data
  logic          tx_str_rdy, rx_str_rdy;  // ready

////////////////////////////////////////////////////////////////////////////////
// TCB read access
////////////////////////////////////////////////////////////////////////////////

  // read configuration/status and RX data
  always_comb
  case (tcb_rdc.req.adr[6-1:0])
    // TX channel
    6'h00:   tcb_rdc.rsp.rdt =                 'x                  ;  // TX data
    6'h04:   tcb_rdc.rsp.rdt =                      32'(tx_sts_cnt);  // TX FIFO load
    6'h08:   tcb_rdc.rsp.rdt = (CFG_RSP_MIN) ? 'x : 32'(tx_cfg_bdr);  // TX baudrate
    6'h0C:   tcb_rdc.rsp.rdt =                 'x                  ;  // TX reserved
    6'h10:   tcb_rdc.rsp.rdt = (CFG_RSP_MIN) ? 'x : 32'(tx_cfg_irq);  // TX interrupt trigger level
    // RX channel
    6'h20:   tcb_rdc.rsp.rdt =                      32'(rx_bus_dat);  // RX data
    6'h24:   tcb_rdc.rsp.rdt =                      32'(rx_sts_cnt);  // RX FIFO load
    6'h28:   tcb_rdc.rsp.rdt = (CFG_RSP_MIN) ? 'x : 32'(rx_cfg_bdr);  // RX baudrate
    6'h2C:   tcb_rdc.rsp.rdt = (CFG_RSP_MIN) ? 'x : 32'(rx_cfg_smp);  // RX sample phase
    6'h30:   tcb_rdc.rsp.rdt = (CFG_RSP_MIN) ? 'x : 32'(rx_cfg_irq);  // RX interrupt trigger level
    // default
    default: tcb_rdc.rsp.rdt =                 'x                  ;
  endcase

  // RX FIFO read ready (write enable signal is not checked)
  assign rx_bus_rdy = tcb_rdc.trn & (tcb_rdc.req.adr[6-1:0] == 6'h20);

  // controller response is immediate
  assign tcb_rdc.rdy = 1'b1;

  // there are no error cases
  assign tcb_rdc.rsp.sts = '0;

////////////////////////////////////////////////////////////////////////////////
// TCB write access
////////////////////////////////////////////////////////////////////////////////

  // write configuration and TX data
  always_ff @(posedge tcb_wrc.clk, posedge tcb_wrc.rst)
  if (tcb_wrc.rst) begin
    // TX channel
    tx_cfg_bdr <= CFG_TX_BDR_RST;
    tx_cfg_irq <= CFG_TX_IRQ_RST;
    // RX channel
    rx_cfg_bdr <= CFG_RX_BDR_RST;
    rx_cfg_smp <= CFG_RX_SMP_RST;
    rx_cfg_irq <= CFG_RX_IRQ_RST;
  end else if (tcb_wrc.trn) begin
    // write access (write enable is not checked)
      case (tcb_wrc.req.adr[6-1:0])
      // TX channel
      6'h00:    /* write data goes directly into the TX FIFO */         ;  // TX data
      6'h04:                                                            ;  // TX FIFO load
      6'h08:   if (CFG_TX_BDR_WEN) tx_cfg_bdr <= tcb_wrc.req.wdt[RW-1:0];  // TX baudrate
      6'h0C:                                                            ;  // TX reserved
      6'h10:   if (CFG_TX_IRQ_WEN) tx_cfg_irq <= tcb_wrc.req.wdt[CW-1:0];  // TX interrupt trigger level
      // RX channel
      6'h20:                                                            ;  // RX data
      6'h24:                                                            ;  // RX FIFO load
      6'h28:   if (CFG_RX_BDR_WEN) rx_cfg_bdr <= tcb_wrc.req.wdt[RW-1:0];  // RX baudrate
      6'h2C:   if (CFG_RX_SMP_WEN) rx_cfg_smp <= tcb_wrc.req.wdt[RW-1:0];  // RX sample phase
      6'h30:   if (CFG_RX_IRQ_WEN) rx_cfg_irq <= tcb_wrc.req.wdt[CW-1:0];  // RX interrupt trigger level
      // default
      default: ;  // do nothing
    endcase
  end

  // TX FIFO write valid (write enable signal is not checked)
  assign tx_bus_vld = tcb_wrc.trn & (tcb_wrc.req.adr[6-1:0] == 6'h00);
  assign tx_bus_dat = tcb_wrc.req.wdt[DW-1:0];

  // controller response is immediate
  assign tcb_wrc.rdy = 1'b1;

  // there are no error cases
  assign tcb_wrc.rsp.sts = '0;

////////////////////////////////////////////////////////////////////////////////
// TX channel
////////////////////////////////////////////////////////////////////////////////

  // FIFO
  tcb_uart_fifo #(
    .SZ      (SZ),
  //.AW      (AW),
  //.CW      (CW),
    .DW      (DW)
  ) tx_fifo (
    // system signals
    .clk     (tcb_wrc.clk),
    .rst     (tcb_wrc.rst),
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
    .RW      (RW),
    .DW      (DW)
  ) tx_ser (
    // system signals
    .clk     (tcb_wrc.clk),
    .rst     (tcb_wrc.rst),
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
  tcb_uart_fifo #(
    .SZ      (SZ),
    .AW      (AW),
  //.CW      (8),
    .DW      (DW)
  ) rx_fifo (
    // system signals
    .clk     (tcb_rdc.clk),
    .rst     (tcb_rdc.rst),
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
    .RW      (RW),
    .DW      (DW)
  ) rx_des (
    // system signals
    .clk     (tcb_rdc.clk),
    .rst     (tcb_rdc.rst),
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

endmodule: tcb_ind_uart

