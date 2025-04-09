////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library RISC-V to MEMORY mode conversion
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

module tcb_lib_riscv2memory
  import tcb_pkg::*;
(
  // interfaces
  tcb_if.sub sub,    // TCB subordinate port (manager     device connects here)
  tcb_if.man man,    // TCB manager     port (subordinate device connects here)
  // subordinate port control/status
  output logic mal   // misaligned access
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
  // comparing subordinate and manager interface parameters
  generate
// TODO: this is a converter, parameters will not match
//    if (sub.PHY != man.PHY)  $error("ERROR: %m parameter (sub.PHY = %p) != (man.PHY = %p)", sub.PHY, man.PHY);
  endgenerate
`endif

// TODO: REFERENCE mode with ASCENDING byte order is not supported

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;

  // request
  assign man.req.cmd = sub.req.cmd;
  assign man.req.wen = sub.req.wen;
  assign man.req.ndn = sub.req.ndn;

////////////////////////////////////////////////////////////////////////////////
// address alignment
////////////////////////////////////////////////////////////////////////////////

  // decodings for read and write access are identical
  always_comb
  unique case (sub.req.siz)
    'd0    : mal = 1'b0;
    'd1    : mal = |sub.req.adr[0:0];
    'd2    : mal = |sub.req.adr[1:0];
    'd3    : mal = |sub.req.adr[2:0];
    default: mal = 1'bx;
  endcase

////////////////////////////////////////////////////////////////////////////////
// write/read data
////////////////////////////////////////////////////////////////////////////////

  // write/read data packed arrays
  logic [sub.PHY_BEN-1:0][sub.PHY.UNT-1:0] sub_req_wdt, sub_rsp_rdt;
  logic [man.PHY_BEN-1:0][man.PHY.UNT-1:0] man_req_wdt, man_rsp_rdt;

  // request/response data byte enable
  logic [sub.PHY_BEN-1:0] req_ben;
  logic [sub.PHY_BEN-1:0] rsp_ben;
  
  // response unsigned
  logic rsp_uns;

  // write/read data multiplexer select
  logic [$clog2(sub.PHY_BEN)-1:0] req_sel [man.PHY_BEN-1:0];
  logic [$clog2(sub.PHY_BEN)-1:0] rsp_sel [man.PHY_BEN-1:0];

  // address segment
  int siz;
  logic [$clog2(sub.PHY_BEN)-1:0] adr;

  // address segment
  assign siz = 2**sub.req.siz;
  assign adr = sub.req.adr[$clog2(sub.PHY_BEN)-1:0];

  // write/read data packed array to/from vector
  assign sub_req_wdt = sub.req.wdt;
  assign sub.rsp.rdt = sub_rsp_rdt;

  // RISC-V to MEMORY mode conversion
  generate

    // mask unaligned address bits
    if (sub.PHY.ALW > 0) begin: alignment
      assign man.req.adr = {sub.req.adr[sub.PHY.ADR-1:sub.PHY.ALW], sub.PHY.ALW'('0)};
    end: alignment
    else begin
      assign man.req.adr = sub.req.adr;
    end

    // byte mapping and signed/unsigned extension
    for (genvar i=0; i<man.PHY_BEN; i++) begin: byteenable

      // multiplexer select signal (little/big endian)
      always_comb
      case (sub.req.ndn)
        TCB_LITTLE:  req_sel[i] = (adr       + i) % sub.PHY_BEN;
        TCB_BIG   :  req_sel[i] = (adr + siz - i) % sub.PHY_BEN;
      endcase

      // byte enable
      assign req_ben[i] = (i >= adr) & (i < adr+siz);

      // multiplexer
      assign man_req_wdt[i] = req_ben[        i ] ? sub_req_wdt[req_sel[i]] : 'x;
      assign sub_rsp_rdt[i] = rsp_ben[rsp_sel[i]] ? man_rsp_rdt[rsp_sel[i]] : (rsp_uns ? '0 : {sub.PHY.UNT{man_rsp_rdt[(adr+siz-1) % sub.PHY_BEN][sub.PHY.UNT-1]}});
    end: byteenable

  endgenerate

  // delay man_rsp_rdt
  // TODO: this now only works for DLY=1, generalize it
  always_ff @(posedge sub.clk)
  begin
    rsp_sel <=     req_sel;
    rsp_ben <=     req_ben;
    rsp_uns <= sub.req.uns;
  end

  // write/read data packed array to/from vector
  assign man.req.ben =     req_ben;
  assign man.req.wdt = man_req_wdt;
  assign man_rsp_rdt = man.rsp.rdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // error
  assign sub.rsp.sts = man.rsp.sts;

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_riscv2memory
