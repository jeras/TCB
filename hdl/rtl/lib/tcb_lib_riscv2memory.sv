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
  tcb_if.man man     // TCB manager     port (subordinate device connects here)
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
// write/read data
////////////////////////////////////////////////////////////////////////////////

  // request/response data packed arrays
  logic [sub.PHY_BEN-1:0][sub.PHY.UNT-1:0] sub_req_wdt, sub_rsp_rdt;
  logic [man.PHY_BEN-1:0][man.PHY.UNT-1:0] man_req_wdt, man_rsp_rdt;

  // byte enable
  logic [sub.PHY_BEN-1:0]                  sub_req_ben             ;

  // request/response address segment
  logic [sub.PHY_OFF-1:0]                      req_off,     rsp_off;

  // request/response endianness
  logic                                        req_ndn,     rsp_ndn;

////////////////////////////////////////////////////////////////////////////////
// address alignment
////////////////////////////////////////////////////////////////////////////////

  // request/response address segment
  assign req_off = sub.dly[0          ].off;
  assign rsp_off = sub.dly[sub.PHY.DLY].off;

  // mask unaligned address bits
  generate
    if (sub.PHY.ALN > 0) begin: alignment
      assign man.req.adr = {sub.req.adr[sub.PHY.ADR-1:sub.PHY.ALN], sub.PHY.ALN'('0)};
    end: alignment
    else begin
      assign man.req.adr = sub.req.adr;
    end
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// multiplexers
////////////////////////////////////////////////////////////////////////////////

  // request/response endianness
  assign req_ndn = sub.req             .ndn;
  assign rsp_ndn = sub.dly[sub.PHY.DLY].ndn;

  // RISC-V mode (subordinate interface) byte enable
  always_comb
  for (int unsigned i=0; i<sub.PHY_BEN; i++) begin: ben_riscv
    sub_req_ben[i] = (i < 2**sub.req.siz) ? 1'b1 : 1'b0;
  end: ben_riscv

  // write/read data packed array to/from vector
  assign sub_req_wdt = sub.req.wdt;
  assign sub.rsp.rdt = sub_rsp_rdt;

  // TODO: do not implement rotations if misaligned accesses are not implemented.
  // request path multiplexer (little/big endian)
  always_comb
  for (int unsigned i=0; i<sub.PHY_BEN; i++) begin: req_riscv2memory
    unique case (sub.req.ndn)
      TCB_LITTLE: begin
        man.req.ben[i] = sub_req_ben[(            (i-req_off)) % sub.PHY_BEN];
        man_req_wdt[i] = sub_req_wdt[(            (i-req_off)) % sub.PHY_BEN];
      end
      TCB_BIG   : begin
        man.req.ben[i] = sub_req_ben[(sub.PHY_BEN-(i-req_off)) % sub.PHY_BEN];
        man_req_wdt[i] = sub_req_wdt[(sub.PHY_BEN-(i-req_off)) % sub.PHY_BEN];
      end
    endcase
  end: req_riscv2memory

  // response path multiplexer
  // TODO: do not implement rotations if misaligned accesses are not implemented.
  // request path multiplexer (little/big endian)
  always_comb
  for (int unsigned i=0; i<sub.PHY_BEN; i++) begin: rsp_riscv2memory
    unique case (sub.req.ndn)
      TCB_LITTLE: begin
        sub_rsp_rdt[i] = man_rsp_rdt[(            (i+rsp_off)) % sub.PHY_BEN];
      end
      TCB_BIG   : begin
        sub_rsp_rdt[i] = man_rsp_rdt[(sub.PHY_BEN-(i+rsp_off)) % sub.PHY_BEN];
      end
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
