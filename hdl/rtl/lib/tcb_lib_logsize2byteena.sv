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

module tcb_lib_logsize2byteena
  import tcb_pkg::*;
#(
  // The ALIGNED implementation should be better optimized for FPGA synthesis
  parameter bit ALIGNED = 1'b1
)(
  // interfaces
  tcb_if.sub sub,    // TCB subordinate port (manager     device connects here)
  tcb_if.man man     // TCB manager     port (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

  initial begin
    // data sizing mode
    assert (sub.BUS.MOD == TCB_MOD_LOG_SIZE) else $error("mismatch (sub.BUS.MOD = %0s) != TCB_MOD_LOG_SIZE", sub.BUS.MOD.name());
    assert (man.BUS.MOD == TCB_MOD_BYTE_ENA) else $error("mismatch (man.BUS.MOD = %0s) != TCB_MOD_BYTE_ENA", man.BUS.MOD.name());
    // other parameters
    assert (      sub.BUS.FRM  ==       man.BUS.FRM ) else $error("mismatch (      sub.BUS.FRM  = %0d) != (      man.BUS.FRM  = %0d)",       sub.BUS.FRM       ,       man.BUS.FRM       );
    assert (      sub.BUS.CHN  ==       man.BUS.CHN ) else $error("mismatch (      sub.BUS.CHN  = %0s) != (      man.BUS.CHN  = %0s)",       sub.BUS.CHN.name(),       man.BUS.CHN.name());
    assert (      sub.BUS.PRF  ==       man.BUS.PRF ) else $error("mismatch (      sub.BUS.PRF  = %0s) != (      man.BUS.PRF  = %0s)",       sub.BUS.PRF.name(),       man.BUS.PRF.name());
    assert ($bits(sub.req.adr) == $bits(man.req.adr)) else $error("mismatch ($bits(sub.req.adr) = %0d) != ($bits(man.req.adr) = %0d)", $bits(sub.req.adr)      , $bits(man.req.adr)      );
    assert (      sub.BUS.NXT  ==       man.BUS.NXT ) else $error("mismatch (      sub.BUS.NXT  = %0s) != (      man.BUS.NXT  = %0s)",       sub.BUS.NXT.name(),       man.BUS.NXT.name());
    assert (      sub.BUS.NDN  ==       man.BUS.NDN ) else $error("mismatch (      sub.BUS.NDN  = %0s) != (      man.BUS.NDN  = %0s)",       sub.BUS.NDN.name(),       man.BUS.NDN.name());
  end

  generate
    if (sub.BUS.CHN != TCB_CHN_READ_ONLY) begin
      initial assert ($bits(sub.req.wdt) == $bits(man.req.wdt)) else $error("mismatch ($bits(sub.req.wdt) = %0d) != ($bits(man.req.wdt) = %0d)", $bits(sub.req.wdt), $bits(man.req.wdt));
    end
    if (sub.BUS.CHN != TCB_CHN_WRITE_ONLY) begin
      initial assert ($bits(sub.rsp.rdt) == $bits(man.rsp.rdt)) else $error("mismatch ($bits(sub.rsp.rdt) = %0d) != ($bits(man.rsp.rdt) = %0d)", $bits(sub.rsp.rdt), $bits(man.rsp.rdt));
    end
  endgenerate

// TODO: this file need a proper testbench and a serious cleanup

  // local parameters derived from the byte enable side (manager)
  localparam BUS_BEN = $bits(man.req.ben);
  localparam BUS_MAX = $clog2(BUS_BEN);

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;

  // request
  generate
    // framing
    if (man.BUS.FRM > 0) begin
      assign man.req.frm = sub.req.frm;
      assign man.req.len = sub.req.len;
    end
    // channel
    if (man.BUS.CHN inside {TCB_CHN_FULL_DUPLEX, TCB_CHN_HALF_DUPLEX}) begin
      assign man.req.wen = sub.req.wen;
    end
    if (man.BUS.CHN inside {TCB_CHN_FULL_DUPLEX}) begin
      assign man.req.ren = sub.req.ren;
    end
    // prefetch
    if (man.BUS.PRF == TCB_PRF_ENABLED) begin
      assign man.req.rpt = sub.req.rpt;
      assign man.req.inc = sub.req.inc;
    end
    // address and next address
    assign man.req.adr = sub.req.adr;
    if (man.BUS.NXT == TCB_NXT_ENABLED) begin
      assign man.req.nxt = sub.req.nxt;
    end
    // request/write data bus
    if (man.BUS.CHN != TCB_CHN_READ_ONLY) begin
    end
    // response/read data bus and data sizing
    if (man.BUS.CHN != TCB_CHN_READ_ONLY) begin
    end
    // endianness
    if (man.BUS.NDN == TCB_NDN_BI_NDN) begin
      assign man.req.ndn = sub.req.ndn;
    end
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // request/response address segment, mask
  logic [BUS_MAX-1:0] req_off, rsp_off;

  // prefix OR operation
  function automatic [BUS_MAX-1:0] prefix_or (logic [BUS_MAX-1:0] val);
    prefix_or[BUS_MAX-1] = val[BUS_MAX-1];
    for (int unsigned i=BUS_MAX-1; i>0; i--) begin
      prefix_or[i-1] = prefix_or[i] | val[i-1];
    end
  endfunction: prefix_or

  // request/response address segment
  assign req_off = sub.req_dly[0          ].adr[BUS_MAX-1:0];
  assign rsp_off = sub.req_dly[sub.HSK_DLY].adr[BUS_MAX-1:0];

////////////////////////////////////////////////////////////////////////////////
// multiplexers
////////////////////////////////////////////////////////////////////////////////

  generate
  if (ALIGNED) begin: aligned

    // offset mask
    logic [BUS_MAX-1:0] req_msk;

    // offset mask
    always_comb
    for (int unsigned i=0; i<BUS_MAX; i++) begin
      req_msk[i] = (i >= sub.req.siz);
    end

    // byte enable
    always_comb
    for (int unsigned i=0; i<BUS_BEN; i++) begin
      man.req.ben[i] = (req_off & req_msk) == (i[BUS_MAX-1:0] & req_msk);
    end

    if (sub.BUS.CHN != TCB_CHN_READ_ONLY) begin: write
      // write access
      always_comb
      for (int unsigned i=0; i<BUS_BEN; i++) begin
        man.req.wdt[i] = sub.req.wdt[i[BUS_MAX-1:0] & ~req_msk];
      end
    end: write

    if (sub.BUS.CHN != TCB_CHN_WRITE_ONLY) begin: read
      // read access
      always_comb
      for (int unsigned i=0; i<BUS_BEN; i++) begin
        sub.rsp.rdt[i] = man.rsp.rdt[(~prefix_or(i[BUS_MAX-1:0]) & rsp_off) | i[BUS_MAX-1:0]];
      end
    end: read

  end: aligned
  else begin: unaligned

    // byte enable
    logic [BUS_BEN-1:0] sub_req_ben;

    // logarithmic size mode (subordinate interface) byte enable
    always_comb
    for (int unsigned i=0; i<BUS_BEN; i++) begin: logsize2byteena
      sub_req_ben[i] = (i < 2**sub.req.siz) ? 1'b1 : 1'b0;
    end: logsize2byteena

    // byte enable
    always_comb
    for (int unsigned i=0; i<BUS_BEN; i++) begin: ben
      unique case (sub.req.ndn)
        TCB_LITTLE:  man.req.ben[i] = sub_req_ben[(        (i-req_off)) % BUS_BEN];
        TCB_BIG   :  man.req.ben[i] = sub_req_ben[(BUS_BEN-(i-req_off)) % BUS_BEN];
      endcase
    end: ben

    if (sub.BUS.CHN != TCB_CHN_READ_ONLY) begin: write
      // write data
      always_comb
      for (int unsigned i=0; i<BUS_BEN; i++) begin: wdt
        unique case (sub.req.ndn)
          TCB_LITTLE:  man.req.wdt[i] = sub.req.wdt[(        (i-req_off)) % BUS_BEN];
          TCB_BIG   :  man.req.wdt[i] = sub.req.wdt[(BUS_BEN-(i-req_off)) % BUS_BEN];
        endcase
      end: wdt
    end: write

    if (sub.BUS.CHN != TCB_CHN_WRITE_ONLY) begin: read
      // read data
      always_comb
      for (int unsigned i=0; i<BUS_BEN; i++) begin: rdt
        unique case (sub.req_dly[sub.HSK_DLY].ndn)
          TCB_LITTLE:  sub.rsp.rdt[i] = man.rsp.rdt[(        (i+rsp_off)) % BUS_BEN];
          TCB_BIG   :  sub.rsp.rdt[i] = man.rsp.rdt[(BUS_BEN-(i+rsp_off)) % BUS_BEN];
        endcase
      end: rdt
    end: read

  end: unaligned
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // status error
  assign sub.rsp.sts = man.rsp.sts;

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_logsize2byteena
