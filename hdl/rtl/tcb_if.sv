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
  logic           vld;  // valid
  logic           rdy;  // ready

  // request
  typedef struct {
    // optional
    logic           inc;  // incremented address
    logic           rpt;  // repeated address
    logic           lck;  // arbitration lock
    logic           ndn;  // endianness
    // basic
    logic           wen;  // write enable
    logic [ABW-1:0] adr;  // address
    logic [SZW-1:0] siz;  // logarithmic size
    logic [BEW-1:0] ben;  // byte enable
    logic [DBW-1:0] wdt;  // write data
  } tcb_req_t;

  // response
  typedef struct {
    logic [DBW-1:0] rdt;  // read data
    logic           err;  // error response
  } tcb_rsp_t;

  // request/response
  tcb_req_t req;
  tcb_rsp_t rsp;

////////////////////////////////////////////////////////////////////////////////
// local signals (never outputs on modports)
////////////////////////////////////////////////////////////////////////////////

  // handshake related
  logic           trn        ;  // transfer
  logic           idl        ;  // idle

  // response related related
  typedef struct {
    logic           ena;  // enable
    logic [ABW-1:0] adr;  // address
    logic [SZW-1:0] siz;  // logarithmic size
    logic [BEW-1:0] ben;  // byte enable
  } tcb_dly_t;

  tcb_dly_t dly [0:DLY];

  // transfer (valid and ready at the same time)
  assign trn = vld & rdy;

  // TODO: improve description
  // idle (either not valid or currently ending a cycle with a transfer)
  assign idl = ~vld | trn;

  // response combinational
  assign dly[0].ena = trn                          ;  // response valid
  assign dly[0].adr =                  req.adr     ;  // response address
  assign dly[0].siz =                  req.siz     ;  // response logarithmic size
  assign dly[0].ben = trn & ~req.wen ? req.ben : '0;  // response byte enable

  // response pipeline
  generate
  if (DLY > 0) begin: gen_dly
    always @(posedge clk)
    dly[1:DLY] <= dly[0:DLY-1];
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
    // handshake
    output vld,
    input  rdy,
    // request/response
    output req,
    input  rsp,
    // local signals
    input  trn,
    input  idl,
    input  dly
  );

  // monitor
  modport  mon (
    // system signals
    input  clk,
    input  rst,
    // handshake
    input  vld,
    input  rdy,
    // request/response
    input  req,
    input  rsp,
    // local signals
    input  trn,
    input  idl,
    input  dly
  );

  // subordinate
  modport  sub (
    // system signals
    input  clk,
    input  rst,
    // handshake
    input  vld,
    output rdy,
    // request/response
    input  req,
    output rsp,
    // local signals
    input  trn,
    input  idl,
    input  dly
  );

endinterface: tcb_if
