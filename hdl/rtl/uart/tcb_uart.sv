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
  // configuration register parameters (write enable, reset value)
  logic CFG_TX_BDR_WEN = 1'b1,  logic [CW-1:0] CFG_TX_BDR_RST = '0,  // TX baudrate
  logic CFG_TX_IRQ_WEN = 1'b1,  logic [CW-1:0] CFG_TX_IRQ_RST = '0,  // TX interrupt level
  logic CFG_RX_BDR_WEN = 1'b1,  logic [CW-1:0] CFG_RX_BDR_RST = '0,  // RX baudrate
  logic CFG_RX_SMP_WEN = 1'b1,  logic [CW-1:0] CFG_RX_SMP_RST = '0,  // RX sample
  logic CFG_RX_IRQ_WEN = 1'b1,  logic [CW-1:0] CFG_RX_IRQ_RST = '0,  // RX interrupt level
  // TCB parameters
  bit            CFG_RSP_REG = 1'b1,  // register response path (by default the response is registered giving a DLY of 1)
  bit            CFG_RSP_MIN = 1'b0   // minimalistic response implementation
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
  logic [AW-1:0] tx_cfg_irq, rx_cfg_irq;  // level

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

  logic [bus.DW-1:0] bus_rdt;

  // read configuration/status and RX data
  always_comb
  case (bus.adr[6-1:0])
    // TX channel
    6'h00:   bus_rdt =                 'x             ;
    6'h04:   bus_rdt =                      tx_sts_cnt;
    6'h08:   bus_rdt = (CFG_RSP_MIN) ? 'x : tx_cfg_bdr;
    6'h0C:   bus_rdt =                 'x             ;
    6'h10:   bus_rdt = (CFG_RSP_MIN) ? 'x : tx_cfg_irq;
    // RX channel
    6'h20:   bus_rdt =                      rx_bus_dat;
    6'h24:   bus_rdt =                      rx_sts_cnt;
    6'h28:   bus_rdt = (CFG_RSP_MIN) ? 'x : rx_cfg_bdr;
    6'h2C:   bus_rdt = (CFG_RSP_MIN) ? 'x : rx_cfg_smp;
    6'h30:   bus_rdt = (CFG_RSP_MIN) ? 'x : rx_cfg_irq;
    // default
    default: bus_rdt =                 'x             ;
  endcase

// read data response is registered
if (CFG_RSP_REG) begin: gen_rsp_reg

  always_ff @(posedge bus.clk, posedge bus.rst)
  if (bus.rst) begin
    bus.rdt <= '0;
  end else if (bus.trn ) begin
    if (~bus.wen) begin
      bus.rdt <= bus_rdt;
    end
  end

end: gen_rsp_reg
// read data response is combinational
else begin: gen_rsp_cmb
    
  assign bus.rdt = bus_rdt;

end: gen_rsp_cmb

  // write configuration and TX data
  always_ff @(posedge bus.clk, posedge bus.rst)
  if (bus.rst) begin
    // TX channel
    tx_cfg_bdr <= CFG_TX_BDR_RST;
    tx_cfg_irq <= CFG_TX_IRQ_RST;
    // RX channel
    rx_cfg_bdr <= CFG_RX_BDR_RST;
    rx_cfg_smp <= CFG_RX_SMP_RST;
    rx_cfg_irq <= CFG_RX_IRQ_RST;
  end else if (bus.trn) begin
    if (bus.wen) begin
      // write access
      case (bus.adr[6-1:0])
        // TX channel
        6'h00:   ;  // write data goes directly into the TX FIFO
        6'h04:   ;
        6'h08:   if (CFG_TX_BDR_WEN) tx_cfg_bdr <= bus.wdt;
        6'h0C:   ;
        6'h10:   if (CFG_TX_IRQ_WEN) tx_cfg_irq <= bus.wdt;
        // RX channel
        6'h20:   ;
        6'h24:   ;
        6'h28:   if (CFG_RX_BDR_WEN) rx_cfg_bdr <= bus.wdt;
        6'h2C:   if (CFG_RX_SMP_WEN) rx_cfg_smp <= bus.wdt;
        6'h30:   if (CFG_RX_IRQ_WEN) rx_cfg_irq <= bus.wdt;
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