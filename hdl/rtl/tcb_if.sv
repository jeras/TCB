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
  parameter  tcb_phy_t  PHY = TCB_PAR_PHY_DEF,
  parameter  type tcb_req_cmd_t = tcb_req_cmd_def_t,
  parameter  type tcb_rsp_sts_t = tcb_rsp_sts_def_t
)(
  // system signals
  input  logic clk,  // clock
  input  logic rst   // reset
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  // byte enable width (number of units inside data)
  localparam int unsigned PHY_BEN = PHY.DAT / PHY.UNT;

  // offset width (number of address bits defining the offset of units inside data)
  localparam int unsigned PHY_OFF = $clog2(PHY_BEN);

  // logarithmic transfer size width
  localparam int unsigned PHY_SIZ = $clog2(PHY_OFF+1);

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
    logic               ren;  // read enable
    logic               ndn;  // endianness
    logic [PHY.ADR-1:0] adr;  // address
    logic [PHY_SIZ-1:0] siz;  // logarithmic transfer size
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
// transaction handshake and misalignment logic
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
    logic               ndn;  // endianness
    logic [PHY_OFF-1:0] off;  // offset
    logic [PHY.ALN-1:0] aln;  // alignment
    logic [PHY_SIZ-1:0] siz;  // logarithmic transfer size
    logic [PHY_BEN-1:0] ben;  // byte enable
  } dly_t;

  // response pipeline
  dly_t dly [0:PHY.DLY];

  // local offset
  logic [PHY_OFF-1:0] req_off;

  // local alignment
  logic [PHY.ALN-1:0] req_aln;

  // local byte enable
  logic [PHY_BEN-1:0] req_ben;

  // local offset
  assign req_off = req.adr[PHY_OFF-1:0];

  // TODO: this check only works in TCB_LOG_SIZE mode, add check for TCB_BYTE_ENA mode
  // misalignment
  generate
    if (PHY.ALN > 0) begin: misalignment_mask
      always_comb
      begin
        for (int unsigned i=0; i<PHY.ALN; i++) begin
          req_aln[i] = (i < req.siz) ? req.adr[PHY.ALN-1:0] : 1'b0;
        end
      end
    end: misalignment_mask
    else begin
      assign req_aln = 1'b0;
    end
  endgenerate

    // transfer size encoding
  generate
  case (PHY.MOD)
    TCB_LOG_SIZE: begin: byteenable
      for (genvar b=0; b<PHY_BEN; b++) begin
        assign req_ben[b] = b < (2**req.siz);
      end
    end: byteenable
    TCB_BYTE_ENA: begin
      assign req_ben = req.ben;
    end
  endcase
  endgenerate

  // response pipeline combinational input
  assign dly[0].ena = trn                         ;  // valid
  assign dly[0].ren =       req_ren               ;  // read enable
  assign dly[0].ndn =                 req.ndn     ;  // endianness
  assign dly[0].off =                 req_off     ;  // offset
  assign dly[0].aln =                 req_aln     ;  // alignment
  assign dly[0].siz =                 req.siz     ;  // logarithmic transfer size
  assign dly[0].ben = trn & req_ren ? req_ben : '0;  // byte enable

  // response pipeline
  // TODO: avoid toggling if there is not transfer
  generate
  if (PHY.DLY > 0) begin: delay
    always_ff @(posedge clk)
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
