////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus SystemVerilog interface
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

interface tcb_if #(
  // bus widths
  int unsigned AW = 32,    // address width
  int unsigned DW = 32,    // data    width
  int unsigned BW = DW/8,  // byte e. width
    // response delay
  int unsigned DLY = 1

)(
  // system signals
  input  logic clk,  // clock
  input  logic rst   // reset
);

  // system bus
  logic          vld;  // valid
  logic          wen;  // write enable
  logic [AW-1:0] adr;  // address
  logic [BW-1:0] ben;  // byte enable
  logic [DW-1:0] wdt;  // write data
  logic [DW-1:0] rdt;  // read data
  logic          err;  // error
  logic          rdy;  // ready

  // local signals
  logic          trn;  // transfer
  logic          idl;  // idle
  logic          rsp;  // response

  // transfer (valid and ready at the same time)
  assign trn = vld & rdy;
  // idle (either not valid or ending a cycle with a transfer)
  assign idl = ~vld | trn;
  // response (DLY clock periods after transfer)
  generate
  if (DLY == 0) begin: gen_rsp
    assign rsp = trn;
  end: gen_rsp
  // response delay queue
  else begin: gen_dly
    if (DLY == 1) begin: gen_rsp
      always @(posedge clk, posedge rst)
      if (rst)  rsp <= 1'b0;
      else      rsp <= trn & ~wen;
    end: gen_rsp
    else begin: gen_dly
      logic [DLY-1:0] que;
      assign rsp = que[DLY-1];
      always @(posedge clk, posedge rst)
      if (rst)  que <= '0;
      else      que <= {que[DLY-2:0], trn & ~wen};
    end: gen_dly
  end: gen_dly
  endgenerate
 
  // manager
  modport  man (
    // system signals
    input  clk,
    input  rst,
    // system bus
    output vld,
    output wen,
    output adr,
    output ben,
    output wdt,
    input  rdt,
    input  err,
    input  rdy,
    // local signals
    input  trn,
    input  idl,
    input  rsp
  );

  // monitor
  modport  mon (
    // system signals
    input  clk,
    input  rst,
    // system bus
    input  vld,
    input  wen,
    input  adr,
    input  ben,
    input  wdt,
    input  rdt,
    input  err,
    input  rdy,
    // local signals
    input  trn,
    input  idl,
    input  rsp
  );

  // subordinate
  modport  sub (
    // system signals
    input  clk,
    input  rst,
    // system bus
    input  vld,
    input  wen,
    input  adr,
    input  ben,
    input  wdt,
    output rdt,
    output err,
    output rdy,
    // local signals
    input  trn,
    input  idl,
    input  rsp
  );

endinterface: tcb_if