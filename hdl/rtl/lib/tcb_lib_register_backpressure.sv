////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library register slice for backpressure path
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

module tcb_lib_register_backpressure #(
  int unsigned GRN = 1  // bus hold granularity (byte granularity by default)
)(
  tcb_if.sub sub,  // TCB subordinate port (manager     device connects here)
  tcb_if.man man   // TCB manager     port (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
  // camparing subordinate and manager interface parameters
  generate
    // bus widths
    if (sub.ADR != man.ADR)  $error("ERROR: %m parameter (sub.ADR = %d) != (man.ADR = %d)", sub.ADR, man.ADR);
    if (sub.DAT != man.DAT)  $error("ERROR: %m parameter (sub.DAT = %d) != (man.DAT = %d)", sub.DAT, man.DAT);
    if (sub.SLW != man.SLW)  $error("ERROR: %m parameter (sub.SLW = %d) != (man.SLW = %d)", sub.SLW, man.SLW);
    if (sub.BEN != man.BEN)  $error("ERROR: %m parameter (sub.BEN = %d) != (man.BEN = %d)", sub.BEN, man.BEN);
    // response delay
    if (sub.DLY != man.DLY)  $error("ERROR: %m parameter (sub.DLY = %d) != (man.DLY = %d)", sub.DLY, man.DLY);
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// register backpressure path
////////////////////////////////////////////////////////////////////////////////

  // request optional
  logic               tmp_inc;  // incremented address
  logic               tmp_rpt;  // repeated address
  logic               tmp_lck;  // arbitration lock
  // request
  logic               tmp_wen;  // write enable
  logic [sub.ADR-1:0] tmp_adr;  // address
  logic [sub.SIZ-1:0] tmp_siz;  // logarithmic size
  logic [sub.BEN-1:0] tmp_ben;  // byte enable
  logic [sub.DAT-1:0] tmp_wdt;  // write data

  always_ff @(posedge sub.clk)
  begin
    if (sub.vld & sub.rdy & ~man.rdy) begin
      // request optional
      tmp_inc <= sub.inc;
      tmp_rpt <= sub.rpt;
      tmp_lck <= sub.lck;
      // request
      tmp_wen <= sub.wen;
      tmp_siz <= sub.siz;
      tmp_ben <= sub.ben;
      tmp_adr <= sub.adr;
      for (int unsigned i=0; i<sub.BEN; i+=sub.SLW*GRN) begin
        // data granularity
        if (sub.wen & sub.ben[i]) begin
          tmp_wdt[i+:sub.SLW*GRN] <= sub.wdt[i+:sub.SLW*GRN];
        end
      end
    end
  end

  // handshake
  assign man.vld = sub.rdy ? sub.vld : 1'b1   ;
  // request optional
  assign man.inc = sub.rdy ? sub.inc : tmp_inc;
  assign man.rpt = sub.rdy ? sub.rpt : tmp_rpt;
  assign man.lck = sub.rdy ? sub.lck : tmp_lck;
  // request
  assign man.wen = sub.rdy ? sub.wen : tmp_wen;
  assign man.siz = sub.rdy ? sub.siz : tmp_siz;
  assign man.ben = sub.rdy ? sub.ben : tmp_ben;
  assign man.adr = sub.rdy ? sub.adr : tmp_adr;
  assign man.wdt = sub.rdy ? sub.wdt : tmp_wdt;

  // response
  assign sub.rdt = man.rdt;
  assign sub.err = man.err;

  // handshake
  always_ff @(posedge sub.clk, posedge sub.rst)
  if (sub.rst) begin
    sub.rdy <= 1'b1;
  end else begin
    if (sub.rdy)  sub.rdy <= ~(sub.vld & ~man.rdy);
    else          sub.rdy <=              man.rdy ;
  end

endmodule: tcb_lib_register_backpressure
