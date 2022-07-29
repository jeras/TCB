////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus passthrough
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

module tcb_pas (
  tcb_if.sub sub,  // TCB subordinate port (manager     device connects here)
  tcb_if.man man   // TCB manager     port (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// camparing subordinate and manager interface parameters
if (sub.AW  != man.AW )  $error("ERROR: %m parameter AW  validation failed");
if (sub.DW  != man.DW )  $error("ERROR: %m parameter DW  validation failed");
if (sub.BW  != man.BW )  $error("ERROR: %m parameter SW  validation failed");
if (sub.DLY != man.DLY)  $error("ERROR: %m parameter DLY validation failed");

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

assign man.vld = sub.vld;
assign man.wen = sub.wen;
assign man.ben = sub.ben;
assign man.adr = sub.adr;
assign man.wdt = sub.wdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

assign sub.rdt = man.rdt;
assign sub.err = man.err;
assign sub.rdy = man.rdy;

endmodule: tcb_pas