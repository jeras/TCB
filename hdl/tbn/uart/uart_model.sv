////////////////////////////////////////////////////////////////////////////////
// UART interface model
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

`timescale  1ns / 1ps

module uart_model #(
  int unsigned DW     = 8,          // data width (sizes from 5 to 8 bits are supported)
  int unsigned SW     = 1,          // stop width (one or more stop bits are supported)
  string       PARITY = "NONE",     // parity ("NONE" , "EVEN", "ODD")
  longint      BAUD   = 112_200,    // baud rate
  // data streams
  string       FILE_I = "",         // program filename
  string       FILE_O = "",         // program filename
  // presentation
  string       NAME   = "noname",
  bit          AUTO   = 0
)(
//output logic DTR,  // Data Terminal Ready
//output logic DSR,  // Data Set Ready
//output logic RTS,  // Request To Send
//output logic CTS,  // Clear To Send
//output logic DCD,  // Carrier Detect
//output logic RI,   // Ring Indicator
  output logic TXD,  // Transmitted Data
  input  logic RXD   // Received Data
);

////////////////////////////////////////////////////////////////////////////////
// internal signals
////////////////////////////////////////////////////////////////////////////////

// computing the delay based on the baudrate
localparam time dly = 1_000_000_000/BAUD;

// running status
logic run_tx, run_rx;

//                 TX,     RX ;
int             fp_tx , fp_rx ;  // file pointer
int             fs_tx , fs_rx ;  // file status
int             cnt_tx, cnt_rx;  // bit counter
logic [DW-1:0]  c_tx  , c_rx  ;  // transferred character

// transfer start condition and data sampling events for UART receiver
event sample;

////////////////////////////////////////////////////////////////////////////////
// file handler
////////////////////////////////////////////////////////////////////////////////

// automatic initialization if enabled
initial begin
  $display ("DEBUG: Starting master");
  TXD = 1'b1;
  run_tx = 0;
  run_rx = 0;
  if (AUTO)  start (FILE_I, FILE_O);
end

// start UART model
task start (
  input string filename_tx,
  input string filename_rx
); begin
  // transmit initialization
  cnt_tx = 0;
  if (filename_tx != "") begin
    fp_tx = $fopen (filename_tx, "r");
    $display ("DEBUG: Opening write file for input stream \"%0s\".", filename_tx);
  end
  // receive initialization
  cnt_rx = 0;
  if (filename_rx != "") begin
    fp_rx = $fopen (filename_rx, "w");
    $display ("DEBUG: Opening read file for output stream \"%0s\".", filename_rx);
  end
  run_rx <= 1;
  run_tx <= 1;
end endtask

// stop UART model
task stop; begin
  run_tx = 0;
  run_rx = 0;
  $fclose (fp_tx);
  $fclose (fp_rx);
end endtask

////////////////////////////////////////////////////////////////////////////////
// TX/RX handlers
////////////////////////////////////////////////////////////////////////////////

// transmitter
always @ (posedge run_tx) begin
  while (run_tx) begin
    while ($feof(fp_tx)) begin end
    c_tx = $fgetc(fp_tx);
    tx(c_tx);
    cnt_tx++;
  end
end

always @ (posedge run_rx) begin
  while (run_rx) begin
    rx(c_rx);
    // increment counter and write received character into file
    cnt_rx++;
    fs_tx = $ungetc(c_rx, fp_rx);
  end
end

////////////////////////////////////////////////////////////////////////////////
// TX/RX tasks
////////////////////////////////////////////////////////////////////////////////

// TX
task tx (input logic [DW-1:0] dat);
  // start bit
  TXD = 1'b0; #dly;
  // transmit bits LSB first
  for (int i=0; i<DW; i++) begin
    TXD = dat[i]; #dly;
  end
  // send parity
  case (PARITY)
    "ODD"  : begin  TXD = ~^dat; #dly;  end
    "EVEN" : begin  TXD =  ^dat; #dly;  end
    "NONE" : begin                      end
  endcase
  // stop bits
  for (int i=0; i<SW; i++) begin
    TXD = 1'b1; #dly;
  end
endtask: tx

// RX
task rx (output logic [DW-1:0] dat);
  @(negedge RXD)
  #(dly/2);
  // check the start bit
  if (RXD != 1'b0)  $display ("DEBUG: start bit error."); #dly;
  // sample in the middle of each bit
  for (int i=0; i<DW; i++) begin
    -> sample;
    dat [i] = RXD; #dly;
  end
  // check parity
  case (PARITY)
    "ODD"  : begin  if (RXD != ~^dat)  $display ("DEBUG: parity error."); #dly;  end
    "EVEN" : begin  if (RXD !=  ^dat)  $display ("DEBUG: parity error."); #dly;  end
    "NONE" : begin                                                               end
  endcase
  // check the stop bit
  if (RXD != 1'b1)  $display ("DEBUG: stop bit error.");
endtask: rx

endmodule: uart_model
