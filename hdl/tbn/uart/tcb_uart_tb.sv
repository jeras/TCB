////////////////////////////////////////////////////////////////////////////////
// R5P testbench for core module
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
  import tcb_pkg::*;
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
 
  // TX string
  localparam string str_tx = "Hello, World!";
  localparam int    str_len = str_tx.len();
  // RX string
  byte str_rx [str_len];

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
    man.write('h08, 4'b1111, 32'h00000003, err);  // TX baudrate  (4)
    man.write('h28, 4'b1111, 32'h00000003, err);  // RX baudrate  (4)
    man.write('h2C, 4'b1111, 32'h00000001, err);  // RX sample    (2)
    man.write('h30, 4'b1111, 32'(str_len-1), err);  // RX IRQ level
    // write TX data
    for (int unsigned i=0; i<str_len; i++) begin
      man.write('h00, 4'b1111, 32'(str_tx[i]), err);
    end
    // wait for RX IRQ
    do begin
      @(posedge clk);
    end while (!irq_rx);
    // read RX data
    for (int unsigned i=0; i<str_len; i++) begin
      man.read('h20, 4'b1111, rdt, err);
      str_rx[i] = rdt[UDW-1:0];
    end
    if (string'(str_rx) != str_tx)  $display("ERROR: RX '%s' differs from TX '%s'", str_rx, str_tx);
    // end simulation
    repeat (4) @(posedge clk);
    $finish();
  end

  // timeout
  initial
  begin
    repeat (300) @(posedge clk);
    $finish();
  end

  // TCB manager model
  tcb_man #(
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