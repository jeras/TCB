//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  UART interface model                                                    //
//                                                                          //
//  Copyright (C) 2009  Iztok Jeras                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  This RTL is free hardware: you can redistribute it and/or modify        //
//  it under the terms of the GNU Lesser General Public License             //
//  as published by the Free Software Foundation, either                    //
//  version 3 of the License, or (at your option) any later version.        //
//                                                                          //
//  This RTL is distributed in the hope that it will be useful,             //
//  but WITHOUT ANY WARRANTY; without even the implied warranty of          //
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           //
//  GNU General Public License for more details.                            //
//                                                                          //
//  You should have received a copy of the GNU General Public License       //
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`timescale  1ns / 1ps

module uart_model #(
  parameter DW     = 8,          // data width (sizes from 5 to 8 bits are supported)
  parameter SW     = 1,          // stop width (one or more stop bits are supported)
  parameter IDLE   = 1'b1,       // bus idle state
  parameter PARITY = "NONE",     // parity ("NONE" , "EVEN", "ODD")
  parameter BAUD   = 112_200,    // baud rate
  // data streams
  parameter FILE_I = "",         // program filename
  parameter FILE_O = "",         // program filename
  // presentation
  parameter NAME   = "noname",
  parameter AUTO   = 0
)(
//  output reg  DTR,  // Data Terminal Ready
//  output reg  DSR,  // Data Set Ready
//  output reg  RTS,  // Request To Send
//  output reg  CTS,  // Clear To Send
//  output reg  DCD,  // Carrier Detect
//  output reg  RI,   // Ring Indicator
  output reg  TxD,  // Transmitted Data
  input  wire RxD   // Received Data
);

///////////////////////////////////////////////////////////////////////////////
// computing the delay based on the baudrate                                 //
///////////////////////////////////////////////////////////////////////////////

localparam d = 1_000_000_000/BAUD;

///////////////////////////////////////////////////////////////////////////////
// internal signals                                                          //
///////////////////////////////////////////////////////////////////////////////

// running status
reg run_tx, run_rx;

//            transmitter, receiver   ;
integer       fp_tx , fp_rx ;
integer       fs_tx , fs_rx ;
integer       cnt_tx, cnt_rx;
integer       bit_tx, bit_rx;
reg [DW-1:0]  c_tx  , c_rx  ;  // transferred character

// transfer start condition and data sampling events for UART receiver
event RxD_edge, sample;

///////////////////////////////////////////////////////////////////////////////
// file handler                                                              //
///////////////////////////////////////////////////////////////////////////////

// automatic initialization if enabled
initial begin
  $display ("DEBUG: Starting master");
  TxD = IDLE;
  run_tx = 0;
  run_rx = 0;
  if (AUTO)  start (FILE_I, FILE_O);
end

// start UART model
task start (
  input reg [256*8-1:0] filename_tx,
  input reg [256*8-1:0] filename_rx
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

///////////////////////////////////////////////////////////////////////////////
// receive and transmitt handlers                                             //
///////////////////////////////////////////////////////////////////////////////

// transmitter
always @ (posedge run_tx) begin
  while (run_tx) begin
    while ($feof(fp_tx)) begin end
    c_tx = $fgetc(fp_tx);
    // start bit
    TxD = ~IDLE; #d;
    // transmit bits LSB first
    for (bit_tx=0; bit_tx<DW; bit_tx=bit_tx+1) begin
      //{c_tx [DW-2:0], TxD} = c_tx;
      TxD = c_tx [bit_tx]; #d;
    end
    // send parity
    case (PARITY)
      "ODD"  : begin  TxD = ~^c_tx; #d;  end
      "EVEN" : begin  TxD =  ^c_tx; #d;  end
      "NONE" : begin                     end
    endcase
    // increment counter
    cnt_tx = cnt_tx + 1;
    // stop bits
    for (bit_tx=DW; bit_tx<DW+SW; bit_tx=bit_tx+1) begin
      TxD = IDLE; #d;
    end
  end
end

// receiver
generate
if (IDLE)  always @ (negedge RxD) -> RxD_edge;
else       always @ (posedge RxD) -> RxD_edge;
endgenerate

always @ (posedge run_rx) begin
  while (run_rx) begin
    @ (RxD_edge) begin
      #(d/2);
      // check the start bit
      if (RxD != ~IDLE)  $display ("DEBUG: start bit error."); #d;
      // sample in the middle of each bit
      for (bit_rx=0; bit_rx<DW; bit_rx=bit_rx+1) begin
        //c_rx = {c_rx [DW-2:0], RxD};
        -> sample;
        c_rx [bit_rx] = RxD; #d;
      end
      // check parity
      case (PARITY)
        "ODD"  : begin  if (RxD != ~^c_rx)  $display ("DEBUG: parity error."); #d;  end
        "EVEN" : begin  if (RxD !=  ^c_rx)  $display ("DEBUG: parity error."); #d;  end
        "NONE" : begin                                                              end
      endcase
      // increment counter and write received character into file
      cnt_rx = cnt_rx + 1;
      fs_tx = $ungetc (c_rx, fp_rx);
      // check the stop bit
      if (RxD != IDLE)  $display ("DEBUG: stop bit error.");
    end
  end
end


endmodule
