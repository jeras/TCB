////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library log. size to byte enable mode conversion
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

module tcb_lib_misaligned_memory_controller
  import tcb_pkg::*;
#(
  parameter  int unsigned DAT = 8,
  parameter  int unsigned ADR = 8,
  parameter  int unsigned CEN = 4
)(
  // TCB interface
  tcb_if.sub tcb,  // TCB subordinate port (manager device connects here)
  // SRAM interface
  output logic [CEN-1:0]          cen,  // chip enable
  output logic                    wen,  // write enable
  output logic [CEN-1:0][ADR-1:0] adr,  // address
  output logic [CEN-1:0][DAT-1:0] wdt,  // write data
  input  logic [CEN-1:0][DAT-1:0] rdt   // read data
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

//  // BUS parameters
//  initial begin
//    // data sizing mode
//    assert (sub.BUS.MOD == TCB_MOD_LOG_SIZE) else $error("mismatch (sub.BUS.MOD = %0s) != TCB_MOD_LOG_SIZE", sub.BUS.MOD.name());
//    assert (man.BUS.MOD == TCB_MOD_BYTE_ENA) else $error("mismatch (man.BUS.MOD = %0s) != TCB_MOD_BYTE_ENA", man.BUS.MOD.name());
//    // other parameters
//    assert (      sub.BUS.FRM  ==       man.BUS.FRM ) else $error("mismatch (      sub.BUS.FRM  = %0d) != (      man.BUS.FRM  = %0d)",       sub.BUS.FRM       ,       man.BUS.FRM       );
//    assert (      sub.BUS.CHN  ==       man.BUS.CHN ) else $error("mismatch (      sub.BUS.CHN  = %0s) != (      man.BUS.CHN  = %0s)",       sub.BUS.CHN.name(),       man.BUS.CHN.name());
//    assert (      sub.BUS.PRF  ==       man.BUS.PRF ) else $error("mismatch (      sub.BUS.PRF  = %0s) != (      man.BUS.PRF  = %0s)",       sub.BUS.PRF.name(),       man.BUS.PRF.name());
//    assert ($bits(sub.req.adr) == $bits(man.req.adr)) else $error("mismatch ($bits(sub.req.adr) = %0d) != ($bits(man.req.adr) = %0d)", $bits(sub.req.adr)      , $bits(man.req.adr)      );
//    assert (      sub.BUS.NXT  ==       man.BUS.NXT ) else $error("mismatch (      sub.BUS.NXT  = %0s) != (      man.BUS.NXT  = %0s)",       sub.BUS.NXT.name(),       man.BUS.NXT.name());
//    assert (      sub.BUS.ORD  ==       man.BUS.ORD ) else $error("mismatch (      sub.BUS.ORD  = %0s) != (      man.BUS.ORD  = %0s)",       sub.BUS.ORD.name(),       man.BUS.ORD.name());
//    assert (      sub.BUS.NDN  ==       man.BUS.NDN ) else $error("mismatch (      sub.BUS.NDN  = %0s) != (      man.BUS.NDN  = %0s)",       sub.BUS.NDN.name(),       man.BUS.NDN.name());
//  end
//
//  generate
//    if (sub.BUS.CHN != TCB_CHN_READ_ONLY) begin
//      initial assert ($bits(sub.req.wdt) == $bits(man.req.wdt)) else $error("mismatch ($bits(sub.req.wdt) = %0d) != ($bits(man.req.wdt) = %0d)", $bits(sub.req.wdt), $bits(man.req.wdt));
//    end
//    if (sub.BUS.CHN != TCB_CHN_WRITE_ONLY) begin
//      initial assert ($bits(sub.rsp.rdt) == $bits(man.rsp.rdt)) else $error("mismatch ($bits(sub.rsp.rdt) = %0d) != ($bits(man.rsp.rdt) = %0d)", $bits(sub.rsp.rdt), $bits(man.rsp.rdt));
//    end
//  endgenerate
//
//  // packeting parameters
//  initial begin
//    assert (sub.PCK.MIN == man.PCK.MIN) else $error("mismatch (sub.PCK.MIN = %0d) != (man.PCK.MIN = %0d)", sub.PCK.MIN, man.PCK.MIN);
//    assert (sub.PCK.OFF == man.PCK.OFF) else $error("mismatch (sub.PCK.OFF = %0d) != (man.PCK.OFF = %0d)", sub.PCK.OFF, man.PCK.OFF);
//    assert (sub.PCK.ALN == man.PCK.ALN) else $error("mismatch (sub.PCK.ALN = %0d) != (man.PCK.ALN = %0d)", sub.PCK.ALN, man.PCK.ALN);
//  end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

//  // request
//  generate
//    // framing
//    if (man.BUS.FRM > 0) begin
//      assign man.req.frm = sub.req.frm;
//      assign man.req.len = sub.req.len;
//    end
//    // channel
//    if (man.BUS.CHN inside {TCB_CHN_FULL_DUPLEX, TCB_CHN_HALF_DUPLEX}) begin
//      assign man.req.wen = sub.req.wen;
//    end
//    if (man.BUS.CHN inside {TCB_CHN_FULL_DUPLEX}) begin
//      assign man.req.ren = sub.req.ren;
//    end
//    // prefetch
//    if (man.BUS.PRF == TCB_PRF_ENABLED) begin
//      assign man.req.rpt = sub.req.rpt;
//      assign man.req.inc = sub.req.inc;
//    end
//    // address and next address
//    assign man.req.adr = sub.req.adr;
//    if (man.BUS.NXT == TCB_NXT_ENABLED) begin
//      assign man.req.nxt = sub.req.nxt;
//    end
//    // endianness
//    if (man.BUS.NDN == TCB_NDN_BI_NDN) begin
//      assign man.req.ndn = sub.req.ndn;
//    end
//  endgenerate

  localparam SRAM_CEN = tcb.BUS.DAT/8/(2**tcn.PCK.off);
  localparam SRAM_ADR = tcb.BUS.ADR - tcb.BUS_MAX;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

//  // request/response address offset, logarithmic size
//  logic [sub.BUS_MAX-1:0] req_off, rsp_off;
//  logic [sub.BUS_SIZ-1:0] req_siz, rsp_siz;
//
//  // endianness
//  logic                   req_ndn, rsp_ndn;
//
//  // prefix OR operation
//  function automatic [sub.BUS_MAX-1:0] prefix_or (
//    input logic [sub.BUS_MAX-1:0] val
//  );
//    prefix_or[sub.BUS_MAX-1] = val[sub.BUS_MAX-1];
//    for (int unsigned i=sub.BUS_MAX-1; i>0; i--) begin
//      prefix_or[i-1] = prefix_or[i] | val[i-1];
//    end
//  endfunction: prefix_or
//
//  // request/response address offset, logarithmic size
//  assign req_off = sub.req_dly[0          ].adr[sub.BUS_MAX-1:0];
//  assign rsp_off = sub.req_dly[sub.HSK_DLY].adr[sub.BUS_MAX-1:0];
//  assign req_siz = sub.req_dly[0          ].siz;
//  assign rsp_siz = sub.req_dly[sub.HSK_DLY].siz;
//
//  // endianness
//  generate
//    case (man.BUS.NDN)
//      BCB_NDN_DEFAULT: begin
//        assign req_ndn = tcb_endian_t'(man.BUS.ORD);
//        assign rsp_ndn = tcb_endian_t'(man.BUS.ORD);
//      end
//      TCB_NDN_LITTLE :  begin
//        assign req_ndn = TCB_LITTLE;
//        assign rsp_ndn = TCB_LITTLE;
//      end
//      TCB_NDN_BIG    :  begin
//        assign req_ndn = TCB_BIG;
//        assign rsp_ndn = TCB_BIG;
//      end
//      TCB_NDN_BI_NDN :  begin
//        assign req_ndn = sub.req.                 ndn;
//        assign rsp_ndn = sub.req_dly[sub.HSK_DLY].ndn;
//      end
//    endcase
//  endgenerate

////////////////////////////////////////////////////////////////////////////////
// multiplexers
////////////////////////////////////////////////////////////////////////////////

  assign cen = {CEN{tcb.vld    }};
  assign wen =      tcb.req.wen  ;
  assign adr = {CEN{tcb.req.adr}};
  assign wdt =      tcb.req.wdt  ;

  assign tcb.req.rdt = rdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // status error
  assign tcb.rsp.sts = '0;

  // handshake
  assign tcb.rdy = 1'b1;

endmodule: tcb_lib_misaligned_memory_controller
