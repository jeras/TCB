////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library register slice for response path
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

module tcb_lib_register_response #(
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
    if (sub.ABW != man.ABW)  $error("ERROR: %m parameter (sub.ABW = %d) != (man.ABW = %d)", sub.ABW, man.ABW);
    if (sub.DBW != man.DBW)  $error("ERROR: %m parameter (sub.DBW = %d) != (man.DBW = %d)", sub.DBW, man.DBW);
    if (sub.SLW != man.SLW)  $error("ERROR: %m parameter (sub.SLW = %d) != (man.SLW = %d)", sub.SLW, man.SLW);
    if (sub.BEW != man.BEW)  $error("ERROR: %m parameter (sub.BEW = %d) != (man.BEW = %d)", sub.BEW, man.BEW);
    // response delay
    if (sub.DLY != man.DLY+1)$error("ERROR: %m parameter (sub.DLY = %d) != (man.DLY = %d)", sub.DLY, man.DLY);
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// register response path
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;

  // request optional
  assign man.inc = sub.inc;
  assign man.rpt = sub.rpt;
  assign man.lck = sub.lck;
  // request
  assign man.wen = sub.wen;
  assign man.siz = sub.siz;
  assign man.ben = sub.ben;
  assign man.adr = sub.adr;
  assign man.wdt = sub.wdt;

  always_ff @(posedge man.clk)
  begin
    // response
    for (int unsigned i=0; i<man.BEW; i+=man.SLW*GRN) begin
      // data granularity
      if (man.rbe[man.DLY][i]) begin
        sub.rdt[i+:man.SLW*GRN] <= man.rdt[i+:man.SLW*GRN];
      end
    end
    sub.err <= man.err;
  end

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_register_response