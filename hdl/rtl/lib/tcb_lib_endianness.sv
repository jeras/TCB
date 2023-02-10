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
#(
)(
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
    if (sub.ABW != man.ABW)  $error("ERROR: %m parameter (sub.ABW = %d) != (man.ABW = %d)", sub.ABW, man.ABW);
    if (sub.DBW != man.DBW)  $error("ERROR: %m parameter (sub.DBW = %d) != (man.DBW = %d)", sub.DBW, man.DBW);
    if (sub.SLW != man.SLW)  $error("ERROR: %m parameter (sub.SLW = %d) != (man.SLW = %d)", sub.SLW, man.SLW);
    if (sub.BEW != man.BEW)  $error("ERROR: %m parameter (sub.BEW = %d) != (man.BEW = %d)", sub.BEW, man.BEW);
    // response delay
    if (sub.DLY != man.DLY)  $error("ERROR: %m parameter (sub.DLY = %d) != (man.DLY = %d)", sub.DLY, man.DLY);
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// misalignment
////////////////////////////////////////////////////////////////////////////////

  // decodings for read and write access are identical
  always_comb
  unique case (sub.siz)
    'd0    : mal = 1'b0;
    'd1    : mal = |sub.adr[0:0];
    'd2    : mal = |sub.adr[1:0];
    'd3    : mal = |sub.adr[2:0];
    default: mal = 1'bx;
  endcase

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;

  // request optional
  assign man.inc = sub.inc;
  assign man.rpt = sub.rpt;
  assign man.lck = sub.lck;
  assign man.ndn = sub.ndn;

  // request
  assign man.wen = sub.wen;
  assign man.siz = sub.siz;
  assign man.adr = sub.adr;

  // write data packed arrays
  logic [sub.BEW-1:0][sub.SLW-1:0] sub_wdt;
  logic [man.BEW-1:0][man.SLW-1:0] man_wdt;

  // write data multiplexer select
  logic [$clog2(sub.BEW)-1:0] mux_wdt [man.BEW-1:0];

  // write data packed array from vector
  assign sub_wdt = sub.wdt;

  // write data bytes
  generate
  for (genvar i=0; i<man.BEW; i++) begin

    // multiplexer select signal
    assign mux_wdt[i] = (man.adr[$clog2(sub.BEW)-1:0] + i) % sub.BEW;

    // byte enable
    assign man.ben[i] = '1;

    // multiplexer
    assign man_wdt[i] = sub_wdt[mux_wdt[i]];

  end
  endgenerate

  // write data packed array to vector
  assign man.wdt = man_wdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // read data packed arrays
  logic [man.BEW-1:0][man.SLW-1:0] man_rdt;
  logic [sub.BEW-1:0][sub.SLW-1:0] sub_rdt;

  // read data multiplexer select
  logic [$clog2(sub.BEW)-1:0] mux_rdt [man.BEW-1:0];

  // write data bytes
  generate
  for (genvar i=0; i<man.BEW; i++) begin

    // multiplexer select signal
    assign mux_rdt[i] = man.adr[$clog2(sub.BEW)-1:0];

    // multiplexer
    assign sub_rdt[i] = man_rdt[mux_rdt[i]];

  end
  endgenerate

  // read data packed array to vector
  assign sub.rdt = sub_rdt;

  // error
  assign sub.err = man.err;

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_endianness
