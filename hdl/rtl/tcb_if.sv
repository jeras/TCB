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
  // PHY parameters
  parameter  tcb_phy_t PHY = TCB_PHY_DEF,
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
// VIP response delay
////////////////////////////////////////////////////////////////////////////////

  // TODO: Might have to move the delay outside of the generate,
  //       so it is visible to the VIP regardless if used or not.
  generate
  if (VIP) begin: vip
    rsp_t dly [0:PHY.DLY];
    if (PHY.DLY > 0) begin
      // propagate response through the delay line
      always_ff @(posedge clk)
      dly[1:PHY.DLY] <= dly[0:PHY.DLY-1];
    end
    // delayed response assignment
    assign rsp = dly[PHY.DLY];
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
    // request/response
    output req,
    input  rsp,
    // local signals
    input  trn,
    input  stl,
    input  idl
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
    input  idl
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
    input  idl
  );

endinterface: tcb_if
