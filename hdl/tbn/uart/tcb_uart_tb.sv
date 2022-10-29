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

module tcb_uart_tb
  import tcb_vip_pkg::*;
#(
  // bus widths
  int unsigned AW = 32,    // address width
  int unsigned DW = 32,    // data    width
  int unsigned BW = DW/8,  // byte e. width
  // response delay
  int unsigned DLY = 1
);

  // UART data width
  localparam int unsigned UDW = 8;
 
  // UART baudrate
  localparam int unsigned TX_BDR = 4;         // TX baudrate
  localparam int unsigned RX_BDR = 4;         // RX baudrate
  localparam int unsigned RX_SMP = RX_BDR/2;  // RX sample

  // TX string
  localparam string TX_STR = "Hello, World!";
  localparam int    TX_LEN = TX_STR.len();
  // RX string
  byte rx_str [TX_LEN];

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // TCB interface
  tcb_if #(.AW (AW), .DW (DW)) bus (.clk (clk), .rst (rst));

  // TCB response check values
  logic [DW-1:0] rdt;
  logic          err;

  // UART signals
  logic uart_rxd;  // receive
  logic uart_txd;  // transmit

  // interrupts
  logic irq_tx;    // TX FIFO load is below limit
  logic irq_rx;    // RX FIFO load is above limit

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  initial          clk = 1'b1;
  always #(20ns/2) clk = ~clk;

  // test sequence
  initial
  begin
    // reset sequence
    rst <= 1'b1;
    repeat (4) @(posedge clk);
    rst <= 1'b0;
    repeat (1) @(posedge clk);
    // write configuration
    man.write('h08, 4'b1111, 32'(TX_BDR-1), err);  // TX baudrate
    man.write('h28, 4'b1111, 32'(RX_BDR-1), err);  // RX baudrate
    man.write('h2C, 4'b1111, 32'(RX_SMP-1), err);  // RX sample
    man.write('h30, 4'b1111, 32'(TX_LEN-1), err);  // RX IRQ level
    // write TX data
    for (int unsigned i=0; i<TX_LEN; i++) begin
      man.write('h00, 4'b1111, 32'(TX_STR[i]), err);
    end
    // wait for RX IRQ
    do begin
      @(posedge clk);
    end while (!irq_rx);
    // read RX data
    for (int unsigned i=0; i<TX_LEN; i++) begin
      man.read('h20, 4'b1111, rdt, err);
      rx_str[i] = rdt[UDW-1:0];
    end
    if (string'(rx_str) != TX_STR)  $display("ERROR: RX '%s' differs from TX '%s'", rx_str, TX_STR);
    // end simulation
    repeat (4) @(posedge clk);
    $finish();
  end

  // timeout
  initial
  begin
    repeat (TX_LEN*10*TX_BDR + 100) @(posedge clk);
    $finish();
  end

  // TCB manager model
  tcb_vip_man #(
    // bus widths
    .AW   (AW),
    .DW   (DW),
    // response delay
    .DLY  (DLY)
  ) man (
    .bus  (bus)
  );

  // TCB UART DUT
  tcb_uart #(
    .DW      (UDW)
  ) uart (
    // UART signals
    .uart_txd (uart_txd),
    .uart_rxd (uart_rxd),
    // system bus interface
    .bus      (bus),
    // interrupts
    .irq_tx   (irq_tx),
    .irq_rx   (irq_rx)
  );

  // UART loopback
  assign uart_rxd = uart_txd;

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_uart_tb