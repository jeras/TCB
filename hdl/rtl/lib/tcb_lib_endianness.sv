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

module tcb_lib_endianness
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
    // bus widths
    if (sub.PHY != man.PHY)  $error("ERROR: %m parameter (sub.PHY = %p) != (man.PHY = %p)", sub.PHY, man.PHY);
    // response delay
    if (sub.DLY != man.DLY)  $error("ERROR: %m parameter (sub.DLY = %d) != (man.DLY = %d)", sub.DLY, man.DLY);
  endgenerate
`endif

// TODO: REFERENCE mode with ASCENDING byte order is not supported

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;

  // request optional
  assign man.req.inc = sub.req.inc;
  assign man.req.rpt = sub.req.rpt;
  assign man.req.lck = sub.req.lck;
  assign man.req.ndn = sub.req.ndn;

  // request
  assign man.req.wen = sub.req.wen;

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
  logic [sub.PHY_BEW-1:0][sub.PHY.SLW-1:0] sub_req_wdt, sub_rsp_rdt;
  logic [man.PHY_BEW-1:0][man.PHY.SLW-1:0] man_req_wdt, man_rsp_rdt;

  // write data multiplexer select
  logic [$clog2(sub.PHY_BEW)-1:0] sel_req_wdt [man.PHY_BEW-1:0];
  // read data multiplexer select
  logic [$clog2(sub.PHY_BEW)-1:0] sel_rsp_rdt [man.PHY_BEW-1:0];

  // write/read data packed array from vector
  assign sub_req_wdt = sub.req.wdt;
  assign man_rsp_rdt = man.rsp.rdt;

  generate
  case (sub.PAR_MOD)
    TCB_REFERENCE: begin
      case (man.PAR_MOD)
        TCB_REFERENCE: begin

          // REFERENCE -> REFERENCE
          assign man.req.adr = sub.req.adr;
          assign man.req.siz = sub.req.siz;
        //assign man.req.ben = sub.req.ben;
          assign man_req_wdt = sub_req_wdt;
          assign sub_rsp_rdt = man_rsp_rdt;

        end
        TCB_MEMORY: begin

          // REFERENCE -> MEMORY
          case (sub.PAR_LGN)
            TCB_UNALIGNED: begin
              assign man.req.adr = sub.req.adr;
            end
            TCB_ALIGNED  : begin
              assign man.req.adr = sub.req.adr & sub.ADR_LGN_MSK;
            end
          endcase
          for (genvar i=0; i<man.PHY_BEW; i++) begin
            int siz = 2**sub.req.siz;
            // multiplexer select signal
            always_comb
            case (sub.req.ndn)
              // little endian
              1'b0: begin
                sel_req_wdt[i] = (man.req.adr[$clog2(sub.PHY_BEW)-1:0]       + i) % sub.PHY_BEW;
              end
              1'b1: begin
                sel_req_wdt[i] = (man.req.adr[$clog2(sub.PHY_BEW)-1:0] + siz - i) % sub.PHY_BEW;
              end
            endcase
            // multiplexer
            case (man.PAR_ORD)
              TCB_DESCENDING: begin
                assign man.req.ben[i] = sub.req.ben[              sel_req_wdt[i]];
                assign man_req_wdt[i] = sub_req_wdt[              sel_req_wdt[i]];
                assign sub_rsp_rdt[i] = man_rsp_rdt[              sel_rsp_rdt[i]];
              end
              TCB_ASCENDING : begin
                assign man.req.ben[i] = sub.req.ben[man.PHY.BEW-1-sel_req_wdt[i]];
                assign man_req_wdt[i] = sub_req_wdt[man.PHY.BEW-1-sel_req_wdt[i]];
                assign sub_rsp_rdt[i] = man_rsp_rdt[man.PHY.BEW-1-sel_rsp_rdt[i]];
              end
            endcase
          end

        end
      endcase
    end
    TCB_MEMORY: begin
      case (man.PAR_MOD)
        TCB_REFERENCE: begin

          // MEMORY -> REFERENCE
          // TODO: not a big priority

        end
        TCB_MEMORY: begin

          // MEMORY -> MEMORY
          case (sub.PAR_LGN)
            TCB_UNALIGNED: begin
              assign man.req.adr = sub.req.adr;
            end
            TCB_ALIGNED  : begin
              assign man.req.adr = sub.req.adr & sub.ADR_LGN_MSK;
            end
          endcase
          for (genvar i=0; i<man.PHY_BEW; i++) begin
            if (sub.PAR_ORD == man.PAR_ORD) begin
              // same byte order
              assign man_req_wdt[i] = sub_req_wdt[              sel_req_wdt[i]];
              assign man.req.ben[i] = sub.req.ben[                          i ];
              assign sub_rsp_rdt[i] = man_rsp_rdt[              sel_rsp_rdt[i]];
            end else begin
              // reversed byte order
              assign man_req_wdt[i] = sub_req_wdt[man.PHY_BEW-1-sel_req_wdt[i]];
              assign man.req.ben[i] = sub.req.ben[man.PHY_BEW-1-            i ];
              assign sub_rsp_rdt[i] = man_rsp_rdt[man.PHY_BEW-1-sel_rsp_rdt[i]];
            end
          end

        end
      endcase
    end
  endcase
  endgenerate

  // write/read data packed array to vector
  assign man.req.wdt = man_req_wdt;
  assign sub.rsp.rdt = sub_rsp_rdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // error
  assign sub.rsp.err = man.rsp.err;

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_endianness
