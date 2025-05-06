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
  // comparing subordinate and manager interface parameters
  initial
  begin
    assert (sub.HSK_DLY == man.HSK_DLY) else $fatal(0, "Parameter (sub.HSK_DLY = %p) != (man.HSK_DLY = %p)", sub.HSK_DLY, man.HSK_DLY);
    assert (sub.BUS == man.BUS) else $fatal(0, "Parameter (sub.BUS = %p) != (man.BUS = %p)", sub.BUS, man.BUS);
  end
`endif

////////////////////////////////////////////////////////////////////////////////
// passthrough
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;
  assign sub.rdy = man.rdy;

  // request/response
  assign man.req = sub.req;
  assign sub.rsp = man.rsp;

endmodule: tcb_lib_passthrough
