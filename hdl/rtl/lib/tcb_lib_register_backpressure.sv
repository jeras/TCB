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

module tcb_lib_register_backpressure
  import tcb_pkg::*;
(
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
    if (sub.BUS.ADR != man.BUS.ADR)  $error("ERROR: %m parameter (sub.ADR = %d) != (man.ADR = %d)", sub.BUS.ADR, man.BUS.ADR);
    if (sub.BUS.DAT != man.BUS.DAT)  $error("ERROR: %m parameter (sub.DAT = %d) != (man.DAT = %d)", sub.BUS.DAT, man.BUS.DAT);
    if (sub.BUS.UNT != man.BUS.UNT)  $error("ERROR: %m parameter (sub.UNT = %d) != (man.UNT = %d)", sub.BUS.UNT, man.BUS.UNT);
    // response delay
    if (sub.HSK_DLY != man.HSK_DLY)  $error("ERROR: %m parameter (sub.HSK_DLY = %d) != (man.HSK_DLY = %d)", sub.HSK_DLY, man.HSK_DLY);
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// register backpressure path
////////////////////////////////////////////////////////////////////////////////

  // request optional
  logic                   tmp_inc;  // incremented address
  logic                   tmp_rpt;  // repeated address
  logic                   tmp_lck;  // arbitration lock
  // request
  logic                   tmp_wen;  // write enable
  logic [sub.BUS.ADR-1:0] tmp_adr;  // address
  logic [sub.BUS_SIZ-1:0] tmp_siz;  // logarithmic size
  logic [sub.BUS_BEN-1:0] tmp_ben;  // byte enable
  logic [sub.BUS.DAT-1:0] tmp_wdt;  // write data

  always_ff @(posedge sub.clk)
  begin
    if (sub.vld & sub.rdy & ~man.rdy) begin
      // request optional
      tmp_inc <= sub.req.cmd.inc;
      tmp_rpt <= sub.req.cmd.rpt;
      tmp_lck <= sub.req.cmd.lck;
      // request
      tmp_wen <= sub.req.wen;
      tmp_siz <= sub.req.siz;
      tmp_ben <= sub.req.ben;
      tmp_adr <= sub.req.adr;
      for (int unsigned i=0; i<sub.BUS_BEN; i++) begin
        // data granularity
        if (sub.req.wen & sub.req.ben[i]) begin
          tmp_wdt[sub.BUS.UNT*i+:sub.BUS.UNT] <= sub.req.wdt[sub.BUS.UNT*i+:sub.BUS.UNT];
        end
      end
    end
  end

  // handshake
  assign man.vld = sub.rdy ? sub.vld : 1'b1   ;
  // request optional
  assign man.req.cmd.inc = sub.rdy ? sub.req.cmd.inc : tmp_inc;
  assign man.req.cmd.rpt = sub.rdy ? sub.req.cmd.rpt : tmp_rpt;
  assign man.req.cmd.lck = sub.rdy ? sub.req.cmd.lck : tmp_lck;
  // request
  assign man.req.wen = sub.rdy ? sub.req.wen : tmp_wen;
  assign man.req.siz = sub.rdy ? sub.req.siz : tmp_siz;
  assign man.req.ben = sub.rdy ? sub.req.ben : tmp_ben;
  assign man.req.adr = sub.rdy ? sub.req.adr : tmp_adr;
  assign man.req.wdt = sub.rdy ? sub.req.wdt : tmp_wdt;

  // response
  assign sub.rsp.rdt     = man.rsp.rdt    ;
  assign sub.rsp.sts.err = man.rsp.sts.err;

  // handshake
  always_ff @(posedge sub.clk, posedge sub.rst)
  if (sub.rst) begin
    sub.rdy <= 1'b1;
  end else begin
    if (sub.rdy)  sub.rdy <= ~(sub.vld & ~man.rdy);
    else          sub.rdy <=              man.rdy ;
  end

endmodule: tcb_lib_register_backpressure
