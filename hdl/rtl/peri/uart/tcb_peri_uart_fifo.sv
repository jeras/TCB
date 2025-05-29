////////////////////////////////////////////////////////////////////////////////
// TCB interface UART controller, stream FIFO
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

module tcb_peri_uart_fifo #(
  int unsigned SZ = 32,            // size
  int unsigned DW = 8,             // data width
  int unsigned AW = $clog2(SZ),    // address width (clog2)
  int unsigned CW = $clog2(SZ+1)   // counter width
)(
  // system signals
  input  logic          clk,
  input  logic          rst,
  // parallel stream input
  input  logic          sti_vld,  // valid
  input  logic [DW-1:0] sti_dat,  // data
  output logic          sti_rdy,  // ready
  // parallel stream output
  output logic          sto_vld,  // valid
  output logic [DW-1:0] sto_dat,  // data
  input  logic          sto_rdy,  // ready
  // status
  output logic [CW-1:0] cnt       // load counter
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

//

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // input interface
  logic          sti_trn;  // transfer
  logic [AW-1:0] sti_adr;  // address counter

  // CDC FIFO memory
  (* ram_style ="distributed" *)
  logic [DW-1:0] mem [0:SZ-1];

  // output interface
  logic          sto_trn;  // transfer
  logic [AW-1:0] sto_adr;  // counter

////////////////////////////////////////////////////////////////////////////////
// input interface
////////////////////////////////////////////////////////////////////////////////

  // transfer
  assign sti_trn = sti_vld & sti_rdy;

  // address
  always_ff @(posedge clk, posedge rst)
  if (rst)           sti_adr <= 'd0;
  else if (sti_trn)  sti_adr <= (sti_adr == AW'(SZ-1)) ? 'd0 : sti_adr + 'd1;

  // memory write
  always_ff @ (posedge clk)
  if (sti_trn) mem [sti_adr[AW-1:0]] <= sti_dat;

////////////////////////////////////////////////////////////////////////////////
// output interface
////////////////////////////////////////////////////////////////////////////////

  // transfer
  assign sto_trn = sto_vld & sto_rdy;

  // address
  always_ff @(posedge clk, posedge rst)
  if (rst)           sto_adr <= 'd0;
  else if (sto_trn)  sto_adr <= (sto_adr == AW'(SZ-1)) ? 'd0 : sto_adr + 'd1;

  // asynchronous memory read
  assign sto_dat = mem [sto_adr[AW-1:0]];

////////////////////////////////////////////////////////////////////////////////
// load counter
////////////////////////////////////////////////////////////////////////////////

  // counter binary
  always_ff @(posedge clk, posedge rst)
  if (rst)  cnt <= 'd0;
  else      cnt <= cnt + CW'(sti_trn) - CW'(sto_trn);

  // input ready (not full)
  assign sti_rdy = (cnt != CW'(SZ));

  // output valid (not empty)
  assign sto_vld = (cnt != 'd0);

endmodule: tcb_peri_uart_fifo
