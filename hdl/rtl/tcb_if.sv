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
  parameter  int unsigned HSK_DLY = TCB_HSK_DEF,  // response delay
  // bus parameters (combined into a structure)
  parameter  type bus_t = tcb_bus_t,  // bus parameter type
  parameter  bus_t BUS = TCB_BUS_DEF,
  // packing parameters
  parameter  type pck_t = tcb_pck_t,  // packing parameter type
  parameter  pck_t PCK = TCB_PCK_DEF,
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
// parameter validation
////////////////////////////////////////////////////////////////////////////////

  generate
    // framing (maximum frame length is FRM+1)
    if (BUS.FRM > 0) begin
      // check frame enable bit presence and type
      initial assert ($bits(req.frm) == 1) else
        $error("unexpected type(req.frm) = ", $typename(req.frm));
      // check frame length vector presence and size
      initial assert ($bits(req.len) == $clog2(BUS.FRM+1)) else
        $error("unexpected type(req.len) = ", $typename(req.len));
    end
    // channel
    if (BUS.CHN == TCB_CHN_FULL_DUPLEX) begin
      // read enable signal must be present on full duplex channels
      initial assert ($bits(req.ren) == 1) else
        $error("unexpected type(req.ren) = ", $typename(req.ren));
    end
    // prefetch
    if (BUS.PRF == TCB_PRF_ENABLED) begin
      // prefetch signals rpt/inc must be present
      initial assert ($bits(req.rpt) == 1) else
        $error("unexpected type(req.rpt) = ", $typename(req.rpt));
      initial assert ($bits(req.inc) == 1) else
        $error("unexpected type(req.inc) = ", $typename(req.inc));
    end
    // address and next address
    initial assert ($bits(req.adr) > 0) else
      $error("unexpected type(req.adr) = ", $typename(req.adr));
    if (BUS.NXT == TCB_NXT_ENABLED) begin
      initial assert ($bits(req.adr) == $bits(req.nxt)) else
        $error("unexpected type(req.nxt) = ", $typename(req.nxt));
    end
    // request/write data bus and data sizing
    if (BUS.CHN != TCB_CHN_READ_ONLY) begin
      // check request/write data bus (multiple of 8 and power of 2)
      initial assert (($bits(req.wdt)%8 == 0) && ($bits(req.wdt) == 2**$clog2($bits(req.wdt)))) else
        $error("unexpected type(req.wdt) = ", $typename(req.wdt));
      // check data sizing
      case (BUS.MOD)
        TCB_MOD_LOG_SIZE: begin  // logarithmic size
          initial assert ($bits(req.siz) == $clog2($clog2($bits(req.wdt)/8)+1)) else
            $error("unexpected type(req.siz) = ", $typename(req.siz));
        end
        TCB_MOD_BYTE_ENA: begin  // byte enable
          initial assert ($bits(req.ben) == $bits(req.wdt)/8) else
            $error("unexpected type(req.ben) = ", $typename(req.ben));
        end
      endcase
    end
    // response/read data bus and data sizing
    if (BUS.CHN != TCB_CHN_READ_ONLY) begin
      // check response/read data bus (multiple of 8 and power of 2)
      initial assert (($bits(rsp.rdt)%8 == 0) && ($bits(rsp.rdt) == 2**$clog2($bits(rsp.rdt)))) else
        $error("unexpected type(rsp.rdt) = ", $typename(rsp.rdt));
      // check data sizing
      case (BUS.MOD)
        TCB_MOD_LOG_SIZE: begin  // logarithmic size
          initial assert ($bits(req.siz) == $clog2($clog2($bits(rsp.rdt)/8)+1)) else
            $error("unexpected type(req.siz) = ", $typename(req.siz));
        end
        TCB_MOD_BYTE_ENA: begin  // byte enable
          initial assert ($bits(req.ben) == $bits(rsp.rdt)/8) else
            $error("unexpected type(req.ben) = ", $typename(req.ben));
        end
      endcase
    end
//    // endianness
//    case (BUS.NDN)
//    //BCB_NDN_DEFAULT:
//          TCB_ORD_DESCENDING: begin
//            initial assert ()
//          end
//          TCB_ORD_ASCENDING : begin
//          end
//        endcase
//      TCB_NDN_LITTLE ,
//      TCB_NDN_BIG    ,
//      TCB_NDN_BI_NDN: begin
//        // bi-endian signal presence
//        initial assert ($bits(req.ndn) == 1) else
//          $error("unexpected type(req.ndn) = ", $typename(req.ndn));
//      end
//    endcase
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  // local parameters are calculated from the request
  // TODO: request data might not be available in read only channel configuration
  localparam int unsigned BUS_BEN = BUS.DAT/8;
  localparam int unsigned BUS_MAX = $clog2(BUS_BEN);
  localparam int unsigned BUS_SIZ = $clog2(DEF_MAX+1);

////////////////////////////////////////////////////////////////////////////////
// helper functions
////////////////////////////////////////////////////////////////////////////////

  // TODO: rethink this functionality
  // logarithmic size mode (subordinate interface) byte enable
  function automatic logic [BUS_BEN-1:0] logsize2byteena (
    input logic [BUS_SIZ-1:0] siz
  );
    for (int unsigned i=0; i<BUS_BEN; i++) begin
      logsize2byteena[i] = (i < 2**siz) ? 1'b1 : 1'b0;
    end
  endfunction: logsize2byteena

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

  logic trn_dly [0:HSK_DLY];
  req_t req_dly [0:HSK_DLY];
  rsp_t rsp_dly [0:HSK_DLY];

  generate
    // delay line
    for (genvar i=0; i<=HSK_DLY; i++) begin: dly
      // handshake transfer
      if (i==0) begin: dly_0
        // continuous assignment
        assign trn_dly[i] = trn;
        assign req_dly[i] = req;
        // response assigned by VIP
      end: dly_0
      else begin: dly_i
        // propagate through delay line
        always_ff @(posedge clk)
        begin
                            trn_dly[i] <= trn_dly[i-1];
          if (trn_dly[i-1]) req_dly[i] <= req_dly[i-1];
          if (trn_dly[i-1]) rsp_dly[i] <= rsp_dly[i-1];
        end
      end: dly_i
    end: dly

    if (VIP) begin: vip
      // continuous assignment
      if (HSK_DLY == 0) begin
        assign rsp = trn ? rsp_dly[HSK_DLY] : '{default: 'x};
      end else begin
        assign rsp =       rsp_dly[HSK_DLY];
      end
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
