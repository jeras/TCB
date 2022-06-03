////////////////////////////////////////////////////////////////////////////////
// UART interface model testbench
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
///////////////////////////////////////////////////////////////////////////////

`timescale  1us / 1ps

module uart_tb ();

// master program input and data output files
//localparam M1_P = "hdl/bench/wishbone/wishbone_program.txt";
localparam UART_TX = "hdl/bench/uart/uart_tx.txt";
localparam UART_RX = "hdl/bench/uart/uart_rx.txt";

// UART loop signal
wire loop;

//////////////////////////////////////////////////////////////////////////////
// 
//////////////////////////////////////////////////////////////////////////////

// request for a dumpfile
initial begin
  $dumpfile("test.vcd");
  $dumpvars(0, uart_tb);
  #1000000;
  $finish;
end

//////////////////////////////////////////////////////////////////////////////
// module instances 
//////////////////////////////////////////////////////////////////////////////

uart_model #(
  .BAUD   (14400),
  .PARITY ("ODD"),
  .FILE_I (UART_TX),
  .FILE_O (UART_RX),
  .NAME   ("UART"),
  .AUTO   (1)
) uart (
  .TxD    (loop),
  .RxD    (loop)
);


endmodule
