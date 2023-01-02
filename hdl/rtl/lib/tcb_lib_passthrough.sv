////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library passthrough
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

module tcb_lib_passthrough (
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
    if (sub.ABW != man.ABW)  $error("ERROR: %m parameter (sub.AW  = %d) != (man.ABW = %d)", sub.ABW, man.ABW);
    if (sub.DBW != man.DBW)  $error("ERROR: %m parameter (sub.DW  = %d) != (man.DBW = %d)", sub.DBW, man.DBW);
    if (sub.SLW != man.SLW)  $error("ERROR: %m parameter (sub.SW  = %d) != (man.SLW = %d)", sub.SLW, man.SLW);
    if (sub.BEW != man.BEW)  $error("ERROR: %m parameter (sub.BW  = %d) != (man.BEW = %d)", sub.BEW, man.BEW);
    // response delay
    if (sub.DLY != man.DLY)  $error("ERROR: %m parameter (sub.DLY = %d) != (man.DLY = %d)", sub.DLY, man.DLY);
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// passthrough
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
  // response
  assign sub.rdt = man.rdt;
  assign sub.err = man.err;
  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_passthrough
