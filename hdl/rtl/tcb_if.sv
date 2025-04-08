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

interface tcb_if
  import tcb_pkg::*;
#(
  tcb_par_phy_t  PHY = TCB_PAR_PHY_DEF,
  type tcb_req_cmd_t = tcb_req_cmd_def_t,
  type tcb_rsp_sts_t = tcb_rsp_sts_def_t
)(
  // system signals
  input  logic clk,  // clock
  input  logic rst   // reset
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  // byte enable width
  localparam int unsigned PHY_BEN = PHY.DAT / PHY.UNT;

  // transfer size width calculation
  localparam int unsigned PHY_SIZ = $clog2($clog2(PHY_BEN)+1);

////////////////////////////////////////////////////////////////////////////////
// I/O ports
////////////////////////////////////////////////////////////////////////////////

  // handshake
  logic vld;  // valid
  logic rdy;  // ready

  // request
  typedef struct packed {
    tcb_req_cmd_t       cmd;  // command (optional)
    logic               wen;  // write enable
    logic               ren;  // write enable
    logic               ndn;  // endianness
    logic [PHY.ADR-1:0] adr;  // address
    logic [PHY_SIZ-1:0] siz;  // transfer size
    logic               uns;  // unsigned
    logic [PHY_BEN-1:0] ben;  // byte enable
    logic [PHY.DAT-1:0] wdt;  // write data
  } req_t;

  // response
  typedef struct packed {
    logic [PHY.DAT-1:0] rdt;  // read data
    tcb_rsp_sts_t       sts;  // status (optional)
  } rsp_t;

  // request/response
  req_t req;
  rsp_t rsp;

////////////////////////////////////////////////////////////////////////////////
// transaction handshake logic
////////////////////////////////////////////////////////////////////////////////

  // handshake
  logic trn;  // transfer
  logic stl;  // stall
  logic idl;  // idle

  // transfer (valid and ready at the same time)
  assign trn = vld & rdy;

  // stall (valid while not ready)
  assign stl = vld & ~rdy;

  // TODO: improve description
  // idle (either not valid or ending the current cycle with a transfer)
  assign idl = ~vld | trn;

////////////////////////////////////////////////////////////////////////////////
// request read/write enable logic depending on channel configuration
////////////////////////////////////////////////////////////////////////////////

  // local read enable
  logic req_ren;

  generate
  // hardcoded values for independent channels
  case (PHY.CHN)
    TCB_COMMON_HALF_DUPLEX: begin                                                end
    TCB_COMMON_FULL_DUPLEX: begin                                                end
    TCB_INDEPENDENT_WRITE : begin assign req.ren = 1'b0;  assign req.wen = 1'b1; end
    TCB_INDEPENDENT_READ  : begin assign req.ren = 1'b1;  assign req.wen = 1'b0; end
  endcase
  // read enable is copied from negated write enable cor common half duplex channel
  if (PHY.CHN == TCB_COMMON_HALF_DUPLEX)  assign req_ren = ~req.wen;
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// response logic (never outputs on modports)
////////////////////////////////////////////////////////////////////////////////

  // response pipeline stage
  typedef struct {
    logic               ena;  // enable
    logic               ren;  // read enable
    logic [PHY.ADR-1:0] adr;  // address
    logic [PHY_SIZ-1:0] siz;  // transfer size
    logic               uns;  // unsigned
    logic [PHY_BEN-1:0] ben;  // byte enable
  } dly_t;

  // response pipeline
  dly_t dly [0:PHY.DLY];

  // local byte enable
  logic [PHY_BEN-1:0] req_ben;

  // transfer size encoding
  generate
  if (PHY.MOD == TCB_RISC_V) begin: byteenable
    for (genvar b=0; b<PHY_BEN; b++) begin
      assign req_ben[b] = b < (2**req.siz);
    end
  end: byteenable
  else begin
    assign req_ben = req.ben;
  end
  endgenerate

  // response pipeline combinational input
  assign dly[0].ena = trn                         ;  // response valid
  assign dly[0].ren =       req_ren               ;  // response read enable
  assign dly[0].adr =                 req.adr     ;  // response address
  assign dly[0].siz =                 req.siz     ;  // response logarithmic size
  assign dly[0].ben = trn & req_ren ? req_ben : '0;  // response byte enable

  // response pipeline
  // TODO: avoid toggling if there is not transfer
  generate
  if (PHY.DLY > 0) begin: delay
    always @(posedge clk)
    dly[1:PHY.DLY] <= dly[0:PHY.DLY-1];
  end: delay
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
    input  stl,
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
    input  stl,
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
    input  stl,
    input  idl,
    input  dly
  );

endinterface: tcb_if
