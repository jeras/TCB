////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) LIBrary PASsthrough
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

module tcb_lib_pas (
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
    if (sub.AW  != man.AW )  $error("ERROR: %m parameter (sub.AW  = %d) != (man.AW  = %d)", sub.AW , man.AW );
    if (sub.DW  != man.DW )  $error("ERROR: %m parameter (sub.DW  = %d) != (man.DW  = %d)", sub.DW , man.DW );
    if (sub.SW  != man.SW )  $error("ERROR: %m parameter (sub.SW  = %d) != (man.SW  = %d)", sub.SW , man.SW );
    if (sub.BW  != man.BW )  $error("ERROR: %m parameter (sub.BW  = %d) != (man.BW  = %d)", sub.BW , man.BW );
    // response delay
    if (sub.DLY != man.DLY)  $error("ERROR: %m parameter (sub.DLY = %d) != (man.DLY = %d)", sub.DLY, man.DLY);
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// passthrough
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;
  // request
  assign man.wen = sub.wen;
  assign man.ben = sub.ben;
  assign man.adr = sub.adr;
  assign man.wdt = sub.wdt;
  // request optional
  assign man.lck = sub.lck;
  assign man.rpt = sub.rpt;

  // response
  assign sub.rdt = man.rdt;
  assign sub.err = man.err;
  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_pas
