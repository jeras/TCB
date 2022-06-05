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
  int unsigned DW = 8   // shifter data width
//  parameter string PARITY   = "NONE",         // parity type "EVEN", "ODD", "NONE"
//  parameter int    STOPSIZE = 1,              // number of stop bits
)(
  // UART
  input  logic uart_rxd,  // receive
  output logic uart_txd,  // transmit
  // system bus interface
  tcb_if.sub   bus
);

// FIFO parameters
localparam int unsigned SZ = 32;  // size
//localparam int unsigned DW =  8;  // data width
localparam int unsigned AW =  5;  // address width
//localparam int unsigned CW =  6;  // counter width


// UART transfer length
//localparam UTL = BYTESIZE + (PARITY!="NONE") + STOPSIZE;

// parity option
//localparam CFG_PRT = (PARITY!="EVEN");


//// baudrate signals
//logic    [N_LOG-1:0] txd_bdr, rxd_bdr;
//logic                txd_ena, rxd_ena;

  // TX/RX Fifo stream (between TCB and FIFO)
  logic          txf_vld, rxf_vld; // valid
  logic [DW-1:0] txf_dat, rxf_dat; // data
  logic          txf_rdy, rxf_rdy; // ready
  logic          txf_cnt, rxf_cnt; // counter

  // TX/RX Ser/des stream (between FIFO and SER/DES)
  logic          txs_vld, rxs_vld; // valid
  logic [DW-1:0] txs_dat, rxs_dat; // data
  logic          txs_rdy, rxs_rdy; // ready


////////////////////////////////////////////////////////////////////////////////
// TCB logic
////////////////////////////////////////////////////////////////////////////////

// TCB read data
//assign bus.rdt = {status_rdy, status_err, status_prt, {ADW-BYTESIZE-3{1'b0}}, status_dat};

// interrupt request
//assign irq = status_rdy | status_err;

////////////////////////////////////////////////////////////////////////////////
// UART transmitter FIFO
////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////
// TX channel
////////////////////////////////////////////////////////////////////////////////

  // RX FIFO
  tcb_uart_fifo #(
//    .SZ      (),
    .DW      (DW)
//    .AW      (8),
//    .CW      (8),
  ) tx_fifo (
    // system signals
    .clk     (bus.clk),
    .rst     (bus.rst),
    // parallel stream input
    .sti_vld (txf_vld),
    .sti_dat (txf_dat),
    .sti_rdy (txf_rdy),
    // parallel stream output
    .sto_vld (txs_vld),
    .sto_dat (txs_dat),
    .sto_rdy (txs_rdy),
    // status
    .cnt     (txf_cnt)
  );

  // serializer
  tcb_uart_ser #(
    .CW      (CW),
    .DW      (DW)
  ) ser (
    // system signals
    .clk     (bus.clk),
    .rst     (bus.rst),
    // configuration
    .cfg_bdr (),
    // parallel stream
    .str_vld (txs_vld),
    .str_dat (txs_dat),
    .str_rdy (txs_rdy),
    // serial TX output
    .txd     (uart_txd)
  );

////////////////////////////////////////////////////////////////////////////////
// RX channel
////////////////////////////////////////////////////////////////////////////////

  // RX FIFO
  tcb_uart_fifo #(
//    .SZ      (),
    .DW      (DW)
//    .AW      (8),
//    .CW      (8),
  ) rx_fifo (
    // system signals
    .clk     (bus.clk),
    .rst     (bus.rst),
    // parallel stream input
    .sti_vld (rxs_vld),
    .sti_dat (rxs_dat),
    .sti_rdy (rxs_rdy),
    // parallel stream output
    .sto_vld (rxf_vld),
    .sto_dat (rxf_dat),
    .sto_rdy (rxf_rdy),
    // status
    .cnt     (rxf_cnt)
  );

  // deserializer
  tcb_uart_des #(
    .CW      (CW),
    .DW      (DW)
  ) des (
    // system signals
    .clk     (bus.clk),
    .rst     (bus.rst),
    // configuration
    .cfg_bdr (),
    .cfg_smp (),
    // parallel stream
    .str_vld (rxs_vld),
    .str_dat (rxs_dat),
    // serial RX input
    .rxd     (uart_rxd)
  );

endmodule: tcb_uart