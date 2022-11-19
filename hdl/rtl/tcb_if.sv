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
  // TCB widths
  int unsigned ABW = 32,       // address bus width
  int unsigned DBW = 32,       // data    bus width
  int unsigned SLW =       8,  // selection   width
  int unsigned BEW = DBW/SLW,  // byte enable width
  // response delay
  int unsigned DLY = 1
)(
  // system signals
  input  logic clk,  // clock
  input  logic rst   // reset
);

////////////////////////////////////////////////////////////////////////////////
// I/O ports
////////////////////////////////////////////////////////////////////////////////

  // handshake
  logic           vld;  // handshake valid
  // request optional
  logic           rpt;  // repeat access
  logic           lck;  // arbitration lock
  // request
  logic           wen;  // write enable
  logic [ABW-1:0] adr;  // address
  logic [BEW-1:0] ben;  // byte enable
  logic [DBW-1:0] wdt;  // write data
  // response
  logic [DBW-1:0] rdt;  // read data
  logic           err;  // error response
  // handshake
  logic           rdy;  // handshake ready

////////////////////////////////////////////////////////////////////////////////
// internal signals (never outpus on modports)
////////////////////////////////////////////////////////////////////////////////

  logic           trn;  // transfer
  logic           idl;  // idle
  logic           rsp;  // response
  // TODO: think whether it would make sense to implement delayed wen/ben signals here

  // transfer (valid and ready at the same time)
  assign trn = vld & rdy;

  // TODO: improve description
  // idle (either not valid or currently ending a cycle with a transfer)
  assign idl = ~vld | trn;

  // response valid (DLY clock periods after transfer)
  generate
  if (DLY == 0) begin: gen_rsp
    assign rsp = trn;
  end: gen_rsp
  // response delay queue
  else begin: gen_dly
    if (DLY == 1) begin: gen_rsp
      always @(posedge clk, posedge rst)
      if (rst) begin
        rsp <= 1'b0;
      end else begin
        rsp <= trn;
      end
    end: gen_rsp
    else begin: gen_dly
      logic [DLY-1:0] que;
      assign rsp = que[DLY-1];
      always @(posedge clk, posedge rst)
      if (rst) begin
        que <= '0;
      end else begin
        que <= {que[DLY-2:0], trn};
      end
    end: gen_dly
  end: gen_dly
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// modports
////////////////////////////////////////////////////////////////////////////////

  // manager
  modport  man (
    // system signals
    input  clk,
    input  rst,
    // system bus
    output vld,
    output rpt,
    output lck,
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
    input  rpt,
    input  lck,
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
    input  rpt,
    input  lck,
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