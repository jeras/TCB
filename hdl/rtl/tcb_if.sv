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
  // handshake parameter
  parameter  int unsigned DLY = TCB_DLY_DEF,  // response delay
  // PHY parameters (combined into a structure)
  parameter  type phy_t = tcb_phy_t,  // PHY parameter type
  parameter  phy_t PHY = TCB_PHY_DEF,
  // request/response structure types
  parameter  type req_t = tcb_req_t,  // request
  parameter  type rsp_t = tcb_rsp_t,  // response
  // VIP (not to be used in RTL)
  parameter  bit  VIP = 1'b0 // VIP end node
)(
  // system signals
  input  logic clk,  // clock
  input  logic rst   // reset
);

////////////////////////////////////////////////////////////////////////////////
// I/O ports
////////////////////////////////////////////////////////////////////////////////

  // handshake
  logic vld;  // valid
  logic rdy;  // ready

  // request/response
  req_t req;  // request
  rsp_t rsp;  // response

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  // TODO: rethink whether this fits here, since it depends on req_t
  localparam int unsigned PHY_ADR = $bits(req.adr);
  localparam int unsigned PHY_DAT = $bits(req.wdt);
  localparam int unsigned PHY_BEN = $bits(req.ben);
  localparam int unsigned PHY_SIZ = $bits(req.siz);
  localparam int unsigned PHY_MAX = $clog2(PHY_BEN);

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
// request/response delay
////////////////////////////////////////////////////////////////////////////////

  logic trn_dly [0:DLY];
  req_t req_dly [0:DLY];
  rsp_t rsp_dly [0:DLY];

  generate
    // delay line
    for (genvar i=0; i<=DLY; i++) begin: dly
  
      if (i==0) begin: req_0
        // continuous assignment
        assign req_dly[i] = req;
      end: req_0
      else if (i==1) begin: req_1
        // load on transfer
        always_ff @(posedge clk)
        if (trn) req_dly[i] <= req_dly[i-1];
      end: req_1
      else begin: req_i
        // propagate through delay line
        always_ff @(posedge clk)
        req_dly[i] <= req_dly[i-1];
      end: req_i
  
      if (i==0) begin: rsp_0
        // continuous assignment
        // performed by VIP
      end: rsp_0
      else if (i==1) begin: rsp_1
        // load on transfer
        always_ff @(posedge clk)
        if (trn) rsp_dly[i] <= rsp_dly[i-1];
      end: rsp_1
      else begin: rsp_i
        // propagate through delay line
        always_ff @(posedge clk)
        rsp_dly[i] <= rsp_dly[i-1];
      end: rsp_i
  
    end: dly

    if (VIP) begin: vip
      // continuous assignment
      assign rsp = rsp_dly[DLY];
    end: vip
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
    // local signals
    input  trn,
    input  stl,
    input  idl,
    // request/response
    output req,
    input  rsp,
    // delayed request/response
    input  req_dly,
    input  rsp_dly
  );

  // monitor
  modport  mon (
    // system signals
    input  clk,
    input  rst,
    // handshake
    input  vld,
    input  rdy,
    // local signals
    input  trn,
    input  stl,
    input  idl,
    // request/response
    input  req,
    input  rsp,
    // delayed request/response
    input  req_dly,
    input  rsp_dly
  );

  // subordinate
  modport  sub (
    // system signals
    input  clk,
    input  rst,
    // handshake
    input  vld,
    output rdy,
    // local signals
    input  trn,
    input  stl,
    input  idl,
    // request/response
    input  req,
    output rsp,
    // delayed request/response
    input  req_dly,
    input  rsp_dly
  );

endinterface: tcb_if
