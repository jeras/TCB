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

// TODO: this file need a proper testbench and a serious cleanup

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

  // request/response data packed arrays
  logic [sub.PHY_BEN-1:0][sub.PHY.UNT-1:0] sub_req_wdt, sub_rsp_rdt;
  logic [man.PHY_BEN-1:0][man.PHY.UNT-1:0] man_req_wdt, man_rsp_rdt;

  // byte enable
  logic [sub.PHY_BEN-1:0]                  sub_req_ben             ;

  // request/response address segment
  logic [sub.PHY_LOG-1:0]                      req_adr,     rsp_adr;

  // request/response endianness
  logic                                        req_ndn,     rsp_ndn;

  // request/response address segment
  assign req_adr = sub.req             .adr[sub.PHY_LOG-1:0];
  assign rsp_adr = sub.dly[sub.PHY.DLY].adr[sub.PHY_LOG-1:0];

  // request/response endianness
  assign req_ndn = sub.req             .ndn;
  assign rsp_ndn = sub.dly[sub.PHY.DLY].ndn;

  // write/read data packed array to/from vector
  assign sub_req_wdt = sub.req.wdt;
  assign sub.rsp.rdt = sub_rsp_rdt;

  // mask unaligned address bits
  generate
    if (sub.PHY.ALW > 0) begin: alignment
      assign man.req.adr = {sub.req.adr[sub.PHY.ADR-1:sub.PHY.ALW], sub.PHY.ALW'('0)};
    end: alignment
    else begin
      assign man.req.adr = sub.req.adr;
    end
  endgenerate

  // RISC-V mode (subordinate interface) byte enable
  always_comb
  for (int unsigned i=0; i<sub.PHY_BEN; i++) begin: ben_riscv
    sub_req_ben[i] = (i < 2**sub.req.siz) ? 1'b1 : 1'b0;
  end: ben_riscv

  // TODO: do not implement rotations if misaligned accesses are not implemented.
  // request path multiplexer (little/big endian)
  always_comb
  for (int unsigned i=0; i<sub.PHY_BEN; i++) begin: req_riscv2memory
    unique case (sub.req.ndn)
      TCB_LITTLE: begin
        man.req.ben[i] = sub_req_ben[(            (i-req_adr)) % sub.PHY_BEN];
        man_req_wdt[i] = sub_req_wdt[(            (i-req_adr)) % sub.PHY_BEN];
      end
      TCB_BIG   : begin
        man.req.ben[i] = sub_req_ben[(sub.PHY_BEN-(i-req_adr)) % sub.PHY_BEN];
        man_req_wdt[i] = sub_req_wdt[(sub.PHY_BEN-(i-req_adr)) % sub.PHY_BEN];
      end
//      default   : begin
//        man_req_ben[i] = 'x;
//        man_req_wdt[i] = 'x;
//      end
    endcase
  end: req_riscv2memory

  // response path multiplexer
  // TODO: do not implement rotations if misaligned accesses are not implemented.
  // request path multiplexer (little/big endian)
  always_comb
  for (int unsigned i=0; i<sub.PHY_BEN; i++) begin: rsp_riscv2memory
    unique case (sub.req.ndn)
      TCB_LITTLE: begin
        sub_rsp_rdt[i] = man_rsp_rdt[(            (i+rsp_adr)) % sub.PHY_BEN];
      end
      TCB_BIG   : begin
        sub_rsp_rdt[i] = man_rsp_rdt[(sub.PHY_BEN-(i+rsp_adr)) % sub.PHY_BEN];
      end
//      default   : begin
//        man_req_ben[i] = 'x;
//        man_req_wdt[i] = 'x;
//      end
    endcase
  end: rsp_riscv2memory

  // write/read data packed array to/from vector
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
