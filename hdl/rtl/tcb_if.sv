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
  type tcb_rsp_sts_t = tcb_req_cmd_def_t
)(
  // system signals
  input  logic clk,  // clock
  input  logic rst   // reset
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  // byte enable width
  localparam int unsigned PHY_BEW = PHY.DBW / PHY.SLW;

  // transfer size width calculation
  localparam int unsigned PHY_SZW_LIN = $clog2(       PHY_BEW   );  // linear
  localparam int unsigned PHY_SZW_LOG = $clog2($clog2(PHY_BEW)+1);  // logarithmic (default)
  // transfer size width selection
  localparam int unsigned PHY_SZW = (PHY.SIZ == TCB_LINEAR) ? PHY_SZW_LIN : PHY_SZW_LOG;

  // address alignment mask
  localparam logic [PHY.ABW-1:0] ADR_LGN_MSK = {(PHY.ABW-$clog2(PHY_BEW))'('1), ($clog2(PHY_BEW))'('0)};

////////////////////////////////////////////////////////////////////////////////
// I/O ports
////////////////////////////////////////////////////////////////////////////////

  // handshake
  logic vld;  // valid
  logic rdy;  // ready

  // request
  typedef struct {
    tcb_req_cmd_t       cmd;  // command (optional)
    logic               wen;  // write enable
    logic               ndn;  // endianness
    logic [PHY.ABW-1:0] adr;  // address
    logic [PHY_SZW-1:0] siz;  // transfer size
    logic [PHY_BEW-1:0] ben;  // byte enable
    logic [PHY.DBW-1:0] wdt;  // write data
  } tcb_req_t;

  // response
  typedef struct {
    logic [PHY.DBW-1:0] rdt;  // read data
    tcb_rsp_sts_t       sts;  // status (optional)
  } tcb_rsp_t;

  // request/response
  tcb_req_t req;
  tcb_rsp_t rsp;

////////////////////////////////////////////////////////////////////////////////
// transaction handshake logic
////////////////////////////////////////////////////////////////////////////////

  // handshake
  logic trn;  // transfer
  logic idl;  // idle

  // transfer (valid and ready at the same time)
  assign trn = vld & rdy;

  // TODO: improve description
  // idle (either not valid or ending the current cycle with a transfer)
  assign idl = ~vld | trn;

////////////////////////////////////////////////////////////////////////////////
// response logic (never outputs on modports)
////////////////////////////////////////////////////////////////////////////////

  // response pipeline stage
  typedef struct {
    logic               ena;  // enable
    logic               ren;  // read enable
    logic [PHY.ABW-1:0] adr;  // address
    logic [PHY_SZW-1:0] siz;  // transfer size
    logic [PHY_BEW-1:0] ben;  // byte enable
  } tcb_dly_t;

  // response pipeline
  tcb_dly_t dly [0:PHY.DLY];

  logic [PHY_BEW-1:0] req_ben;  // byte enable

  // copy or create byte enable from transfer size
  generate
  if (PHY.MOD == TCB_REFERENCE) begin
    for (genvar b=0; b<PHY_BEW; b++) begin
      case (PHY.SIZ)
        TCB_LOGARITHMIC:  assign req_ben[b] = b < (2**    req.siz );
        TCB_LINEAR     :  assign req_ben[b] = b < (2**(2**req.siz));
      endcase
    end
  end else begin
    assign req_ben = req.ben;
  end
  endgenerate

  // response pipeline combinational input
  assign dly[0].ena = trn                          ;  // response valid
  assign dly[0].ren =       ~req.wen               ;  // response read enable
  assign dly[0].adr =                  req.adr     ;  // response address
  assign dly[0].siz =                  req.siz     ;  // response logarithmic size
  assign dly[0].ben = trn & ~req.wen ? req_ben : '0;  // response byte enable

  // response pipeline
  // TODO: avoid toggling if there is not transfer
  generate
  if (PHY.DLY > 0) begin: gen_dly
    always @(posedge clk)
    dly[1:PHY.DLY] <= dly[0:PHY.DLY-1];
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
