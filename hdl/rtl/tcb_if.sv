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
  // handshake parameters
  parameter  type hsk_t = tcb_hsk_t,   // handshake parameter type
  parameter  hsk_t HSK = TCB_HSK_DEF,  // handshake parameter
  // bus parameters
  parameter  type bus_t = tcb_bus_t,   // bus parameter type
  parameter  bus_t BUS = TCB_BUS_DEF,  // bus parameter
  // packing parameters
  parameter  type pck_t = tcb_pck_t,   // packing parameter type
  parameter  pck_t PCK = TCB_PCK_DEF,  // packing parameter
  // request/response structure types
  parameter  type req_t = tcb_req_t,   // request
  parameter  type rsp_t = tcb_rsp_t,   // response
  // VIP (not to be used in RTL)
  parameter  type vip_t = tcb_vip_t,   // VIP parameter type
  parameter  vip_t VIP = TCB_VIP_DEF   // VIP parameter
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
    // endianness
    if (BUS.NDN == TCB_NDN_BI_NDN) begin
        // bi-endian signal presence
        initial assert ($bits(req.ndn) == 1) else
          $error("unexpected type(req.ndn) = ", $typename(req.ndn));
    end
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  // local parameters are calculated from the request
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

  // endianness
  // NOTE: If the bus endianness is hardcoded, the transaction endianness must:
  //       - match the hardcoded bus endianness OR,
  //       - be undefined (x/z).
  // NOTE: If the requested endianness $isunknown, the transaction endianness
  //       will be set to the native bus endianness.
  function automatic logic endianness (
    input logic ndn  // requested endianness
  );
    case (BUS.NDN)
      BCB_NDN_DEFAULT: begin
        endianness = BUS.ORD;
        assert (endianness ==? ndn) else $error("Transaction endianness does not match BUS.NDN");
      end
      TCB_NDN_BI_NDN :  begin
        if ($isunknown(ndn)) begin
          endianness = BUS.ORD;
        end else begin
          endianness = ndn;
        end
      end
      TCB_NDN_LITTLE ,
      TCB_NDN_BIG    :  begin
        endianness = BUS.NDN[0];
        assert (endianness ==? ndn) else $error("Transaction endianness does not match BUS.NDN");
      end
    endcase
  endfunction: endianness

  // write enable
  function automatic logic write (
    input logic wen
  );
    case (BUS.CHN)
      TCB_CHN_HALF_DUPLEX:  write =  wen;
      TCB_CHN_FULL_DUPLEX:  write =  wen;
      TCB_CHN_WRITE_ONLY :  write = 1'b1;
      TCB_CHN_READ_ONLY  :  write = 1'b0;
    endcase
  endfunction: write

  // read enable
  function automatic logic read (
    input logic wen,
    input logic ren
  );
    case (BUS.CHN)
      TCB_CHN_HALF_DUPLEX:  read = ~wen;
      TCB_CHN_FULL_DUPLEX:  read =  ren;
      TCB_CHN_WRITE_ONLY :  read = 1'b0;
      TCB_CHN_READ_ONLY  :  read = 1'b1;
    endcase
  endfunction: read

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

  logic trn_dly [0:HSK.DLY];
  req_t req_dly [0:HSK.DLY];
  rsp_t rsp_dly [0:HSK.DLY];

  generate
    // delay line
    for (genvar i=0; i<=HSK.DLY; i++) begin: dly
      // handshake transfer
      if (i==0) begin: dly_0
        // continuous assignment
        assign trn_dly[0] = trn;
        assign req_dly[0] = req;
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

    // TODO implement hold
    if (VIP.DRV) begin: vip
      // continuous assignment
      if (HSK.DLY == 0) begin
        assign rsp = trn ? rsp_dly[HSK.DLY] : '{default: 'z};
      end else begin
        assign rsp =       rsp_dly[HSK.DLY];
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
    input  trn_dly,
    input  req_dly,
    input  rsp_dly,
    // functions
    import endianness,
    import write, read
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
    input  trn_dly,
    input  req_dly,
    input  rsp_dly,
    // functions
    import endianness,
    import write, read
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
    input  trn_dly,
    input  req_dly,
    input  rsp_dly,
    // functions
    import endianness,
    import write, read
  );

endinterface: tcb_if
