////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) SystemVerilog interface
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

// MODES:
// - processor
// - agnostic
// - big-endian
// - little endian

interface tcb_if
  import tcb_pkg::*;
#(
  // TCB widths
  int unsigned ABW = 32,       // address bus width
  int unsigned DBW = 32,       // data    bus width
  int unsigned SLW =       8,  // selection   width
  int unsigned BEW = DBW/SLW,  // byte enable width
  // TCB parameters
  int unsigned DLY = 1,        // response delay
  // other parameters
  tcb_mode_t   MOD = TCB_REFERENCE,
  tcb_order_t  ORD = TCB_DESCENDING,
  tcb_align_t  LGN = TCB_ALIGNED
)(
  // system signals
  input  logic clk,  // clock
  input  logic rst   // reset
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  //
  localparam int unsigned SZW = $clog2($clog2(BEW)+1);  // logarithmic size width

  // address alignment mask
  localparam logic [ABW-1:0] ADR_LGN_MSK = {(ABW-$clog2(BEW))'('1), ($clog2(BEW))'('0)};

////////////////////////////////////////////////////////////////////////////////
// I/O ports
////////////////////////////////////////////////////////////////////////////////

  // handshake
  logic           vld;  // handshake valid
  // request optional
  logic           inc;  // incremented address
  logic           rpt;  // repeated address
  logic           lck;  // arbitration lock
  logic           ndn;  // endianness
  // request
  logic           wen;  // write enable
  logic [ABW-1:0] adr;  // address
  logic [SZW-1:0] siz;  // logarithmic size
  logic [BEW-1:0] ben;  // byte enable
  logic [DBW-1:0] wdt;  // write data
  // response
  logic [DBW-1:0] rdt;  // read data
  logic           err;  // error response
  // handshake
  logic           rdy;  // handshake ready

////////////////////////////////////////////////////////////////////////////////
// internal signals (never outputs on modports)
////////////////////////////////////////////////////////////////////////////////

  // handshake related
  logic           trn        ;  // transfer
  logic           idl        ;  // idle

  // response related (delayed from transfer to response)
  logic           rsp [0:DLY];  // response status
  logic [ABW-1:0] rad [0:DLY];  // response address
  logic [SZW-1:0] rsz [0:DLY];  // response logarithmic size
  logic [BEW-1:0] rbe [0:DLY];  // response byte enable

  // transfer (valid and ready at the same time)
  assign trn = vld & rdy;

  // TODO: improve description
  // idle (either not valid or currently ending a cycle with a transfer)
  assign idl = ~vld | trn;

  // response combinational
  assign rsp[0] = trn                  ;  // response valid
  assign rad[0] =              adr     ;  // response address
  assign rsz[0] =              siz     ;  // response logarithmic size
  assign rbe[0] = trn & ~wen ? ben : '0;  // response byte enable

  // response pipeline
  generate
  for (genvar d=1; d<=DLY; d++) begin: gen_rsp
    always @(posedge clk)
    begin
      rsp[d] <= rsp[d-1];
      rad[d] <= rad[d-1];
      rsz[d] <= rsz[d-1];
      rbe[d] <= rbe[d-1];
    end
  end: gen_rsp
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
    output inc,
    output rpt,
    output lck,
    output ndn,
    output wen,
    output adr,
    output siz,
    output ben,
    output wdt,
    input  rdt,
    input  err,
    input  rdy,
    // local signals
    input  trn,
    input  idl,
    input  rsp,
    input  rad,
    input  rsz,
    input  rbe
  );

  // monitor
  modport  mon (
    // system signals
    input  clk,
    input  rst,
    // system bus
    input  vld,
    input  inc,
    input  rpt,
    input  lck,
    input  ndn,
    input  wen,
    input  adr,
    input  siz,
    input  ben,
    input  wdt,
    input  rdt,
    input  err,
    input  rdy,
    // local signals
    input  trn,
    input  idl,
    input  rsp,
    input  rad,
    input  rsz,
    input  rbe
  );

  // subordinate
  modport  sub (
    // system signals
    input  clk,
    input  rst,
    // system bus
    input  vld,
    input  inc,
    input  rpt,
    input  lck,
    input  ndn,
    input  wen,
    input  adr,
    input  siz,
    input  ben,
    input  wdt,
    output rdt,
    output err,
    output rdy,
    // local signals
    input  trn,
    input  idl,
    input  rsp,
    input  rad,
    input  rsz,
    input  rbe
  );

endinterface: tcb_if
