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
  parameter bit ALIGNED = 1'b1
)(
  // interfaces
  tcb_if.sub sub,    // TCB subordinate port (manager     device connects here)
  tcb_if.man man     // TCB manager     port (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifndef ALTERA_RESERVED_QIS
`else
  // comparing subordinate and manager interface parameters
  initial
  begin
    tcb_bus_match_t match = '{MOD: 1'b0, default: 1'b1};
    // validate TCB BUS.MOD parameter
    assert (sub.BUS.MOD == TCB_LOG_SIZE)
      $fatal("ERROR: %m parameter (sub.BUS.MOD = %s) != TCB_LOG_SIZE", sub.BUS.MOD.name());
    assert (man.BUS.MOD == TCB_BYTE_ENA)
      $fatal("ERROR: %m parameter (sub.BUS.MOD = %s) != TCB_LOG_SIZE", man.BUS.MOD.name());
    // TCB BUS.ORD ASCENDING byte order is not supported
    assert (sub.BUS.MOD != TCB_DESCENDING)
      $fatal("ERROR: %m parameter (sub.BUS.ORD = %s) != TCB_DESCENDING", sub.BUS.ORD.name());
    // validate remaining TCB BUS parameters
    assert tcb_bus_match(sub.BUS, man.BUS, match)
      $fatal("ERROR: %m parameter (sub.BUS = %p) != (man.BUS = %p)", sub.BUS, man.BUS);
  end
`endif

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
  assign man.req.frm = sub.req.frm;
  assign man.req.wen = sub.req.wen;
  assign man.req.ndn = sub.req.ndn;

////////////////////////////////////////////////////////////////////////////////
// write/read data
////////////////////////////////////////////////////////////////////////////////

  // byte enable
  logic [BUS_BEN-1:0] sub_req_ben;

  // request/response address segment, mask
  logic [BUS_MAX-1:0] req_off, rsp_off;
  logic [BUS_MAX-1:0] req_msk, rsp_msk;

  // request/response endianness
  logic               req_ndn, rsp_ndn;

////////////////////////////////////////////////////////////////////////////////
// address alignment
////////////////////////////////////////////////////////////////////////////////

  // request/response address segment
  assign req_off = sub.req_dly[0          ].adr[BUS_MAX-1:0];
  assign rsp_off = sub.req_dly[sub.HSK_DLY].adr[BUS_MAX-1:0];

  // copy address
  assign man.req.adr = sub.req.adr;

////////////////////////////////////////////////////////////////////////////////
// multiplexers
////////////////////////////////////////////////////////////////////////////////

  // request/response endianness
  assign req_ndn = sub.req                 .ndn;
  assign rsp_ndn = sub.req_dly[sub.HSK_DLY].ndn;

  // logarithmic size mode (subordinate interface) byte enable
  always_comb
  for (int unsigned i=0; i<BUS_BEN; i++) begin: logsize2byteena
    sub_req_ben[i] = (i < 2**sub.req.siz) ? 1'b1 : 1'b0;
  end: logsize2byteena

generate
if (ALIGNED) begin

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

    // write access
    always_comb
    for (int unsigned i=0; i<BUS_BEN; i++) begin
      man.req.wdt[i] = sub.req.wdt[i[BUS_MAX-1:0] & ~req_msk];
    end

//    // read access
//    always_comb
//    for (int unsigned i=0; i<BUS_BEN; i++) begin
//      man.req.wdt[i] = sub.req.wdt[$clog2(i)[BUS_MAX-1:0] & rsp_off];
//    end

    logic [4-1:0][8-1:0] tmp_dtw;  // data word
    logic [2-1:0][8-1:0] tmp_dth;  // data half
    logic [1-1:0][8-1:0] tmp_dtb;  // data byte

    // read data multiplexer
    assign tmp_dtw = man.rsp.rdt;
    assign tmp_dth = rsp_off[1] ? tmp_dtw[3:2] : tmp_dtw[1:0];
    assign tmp_dtb = rsp_off[0] ? tmp_dth[1:1] : tmp_dth[0:0];
    // read data multiplexer
    assign sub.rsp.rdt = {tmp_dtw[3:2], tmp_dth[1], tmp_dtb[0]};

  end else begin

    // byte enable
    always_comb
    for (int unsigned i=0; i<BUS_BEN; i++) begin: ben
      unique case (sub.req.ndn)
        TCB_LITTLE:  man.req.ben[i] = sub_req_ben[(        (i-req_off)) % BUS_BEN];
        TCB_BIG   :  man.req.ben[i] = sub_req_ben[(BUS_BEN-(i-req_off)) % BUS_BEN];
      endcase
    end: ben

    // write data
    always_comb
    for (int unsigned i=0; i<BUS_BEN; i++) begin: wdt
      unique case (sub.req.ndn)
        TCB_LITTLE:  man.req.wdt[i] = sub.req.wdt[(        (i-req_off)) % BUS_BEN];
        TCB_BIG   :  man.req.wdt[i] = sub.req.wdt[(BUS_BEN-(i-req_off)) % BUS_BEN];
      endcase
    end: wdt

    // read data
    always_comb
    for (int unsigned i=0; i<BUS_BEN; i++) begin: rdt
      unique case (sub.req.ndn)
        TCB_LITTLE:  sub.rsp.rdt[i] = man.rsp.rdt[(        (i+rsp_off)) % BUS_BEN];
        TCB_BIG   :  sub.rsp.rdt[i] = man.rsp.rdt[(BUS_BEN-(i+rsp_off)) % BUS_BEN];
      endcase
    end: rdt

end
endgenerate

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // error
  assign sub.rsp.sts = man.rsp.sts;

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_logsize2byteena
