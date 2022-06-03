//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  UART interface testbench                                                //
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
