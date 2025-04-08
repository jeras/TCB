////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library mode/alignment/order converter
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

module tcb_lib_converter
  import tcb_pkg::*;
(
  // interfaces
  tcb_if.sub sub,  // TCB subordinate port (manager     device connects here)
  tcb_if.man man,  // TCB manager     port (subordinate device connects here)
  // subordinate port control/status
  output logic mal      // misaligned access
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
  // comparing subordinate and manager interface parameters
  generate
    if (sub.PHY != man.PHY)  $error("ERROR: %m parameter (sub.PHY = %p) != (man.PHY = %p)", sub.PHY, man.PHY);
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

  // write data multiplexer select
  logic [$clog2(sub.PHY_BEN)-1:0] sel_req_wdt [man.PHY_BEN-1:0];
  // read data multiplexer select
  logic [$clog2(sub.PHY_BEN)-1:0] sel_rsp_rdt [man.PHY_BEN-1:0];

  // write/read data packed array from vector
  assign sub_req_wdt = sub.req.wdt;
  assign man_rsp_rdt = man.rsp.rdt;

  generate
  case (sub.PHY.MOD)
    TCB_REFERENCE: begin: sub_reference
      case (man.PHY.MOD)
        TCB_REFERENCE: begin: man_reference

          // REFERENCE -> REFERENCE
          assign man.req.adr = sub.req.adr;
          assign man.req.siz = sub.req.siz;
          assign man.req.ben = sub.req.ben;  // unused
          assign man_req_wdt = sub_req_wdt;
          assign sub_rsp_rdt = man_rsp_rdt;

        end: man_reference
        TCB_MEMORY: begin: man_memory

          // REFERENCE -> MEMORY
          if (sub.PHY.ALW > 0) begin: alignment
            // TODO range should be [max:2]
            assign man.req.adr = {sub.req.adr[sub.PHY.ALW-1:0], sub.PHY.ALW'('0)};
          end: alignment
          else begin
            assign man.req.adr = sub.req.adr;
          end
          for (genvar i=0; i<man.PHY_BEN; i++) begin: byteenable
            int siz = 2**sub.req.siz;
            // multiplexer select signal
            always_comb
            case (sub.req.ndn)
              // little endian
              1'b0: begin: little
                sel_req_wdt[i] = (man.req.adr[$clog2(sub.PHY_BEN)-1:0]       + i) % sub.PHY_BEN;
              end: little
              1'b1: begin: big
                sel_req_wdt[i] = (man.req.adr[$clog2(sub.PHY_BEN)-1:0] + siz - i) % sub.PHY_BEN;
              end: big
            endcase
            // multiplexer
            case (man.PHY.ORD)
              TCB_DESCENDING: begin: descending
                assign man.req.ben[i] = sub.req.ben[              sel_req_wdt[i]];
                assign man_req_wdt[i] = sub_req_wdt[              sel_req_wdt[i]];
                assign sub_rsp_rdt[i] = man_rsp_rdt[              sel_rsp_rdt[i]];
              end: descending
              TCB_ASCENDING : begin: ascending
                assign man.req.ben[i] = sub.req.ben[man.PHY.BEN-1-sel_req_wdt[i]];
                assign man_req_wdt[i] = sub_req_wdt[man.PHY.BEN-1-sel_req_wdt[i]];
                assign sub_rsp_rdt[i] = man_rsp_rdt[man.PHY.BEN-1-sel_rsp_rdt[i]];
              end: ascending
            endcase
          end: byteenable

        end: man_memory
      endcase
    end: sub_reference
    TCB_MEMORY: begin: sub_memory
      case (man.PHY.MOD)
        TCB_REFERENCE: begin: man_reference

          // MEMORY -> REFERENCE
          // TODO: not a big priority

        end: man_reference
        TCB_MEMORY: begin: man_memory

          // MEMORY -> MEMORY
          if (sub.PHY.ALW > 0) begin: alignment
            // TODO range should be [max:2]
            assign man.req.adr = {sub.req.adr[sub.PHY.ALW-1:0], sub.PHY.ALW'('0)};
          end: alignment
          else begin: noalignment
            assign man.req.adr = sub.req.adr;
          end: noalignment
          for (genvar i=0; i<man.PHY_BEN; i++) begin: byteenable
            if (sub.PHY.ORD == man.PHY.ORD) begin: order_same
              // same byte order
              assign man.req.ben[i] = sub.req.ben[              i];
              assign man_req_wdt[i] = sub_req_wdt[              i];
              assign sub_rsp_rdt[i] = man_rsp_rdt[              i];
            end: order_same
            else begin: order_opposite
              // reversed byte order
              assign man.req.ben[i] = sub.req.ben[man.PHY_BEN-1-i];
              assign man_req_wdt[i] = sub_req_wdt[man.PHY_BEN-1-i];
              assign sub_rsp_rdt[i] = man_rsp_rdt[man.PHY_BEN-1-i];
            end: order_opposite
          end: byteenable

        end: man_memory
      endcase
    end: sub_memory
  endcase
  endgenerate

  // write/read data packed array to vector
  assign man.req.wdt = man_req_wdt;
  assign sub.rsp.rdt = sub_rsp_rdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // error
  assign sub.rsp.sts = man.rsp.sts;

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_converter
