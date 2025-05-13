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
    // parameters
    assert (man.HSK_DLY == sub.HSK_DLY) else $error("Parameter (man.HSK_DLY = %p) != (sub.HSK_DLY = %p)", man.HSK_DLY, sub.HSK_DLY);
    assert (man.BUS     == sub.BUS    ) else $error("Parameter (man.BUS     = %p) != (sub.BUS     = %p)", man.BUS    , sub.BUS    );
    assert (man.PCK     == sub.PCK    ) else $error("Parameter (man.PCK     = %p) != (sub.PCK     = %p)", man.PCK    , sub.PCK    );
    // request/response types
    // TODO: Questa is complaining here
//    assert (type(man.req_t) == type(sub.req_t)) else $error("Parameter (man.req_t = %s) != (sub.req_t = %s)", $typename(man.req_t), $typename(sub.req_t));
//    assert (type(man.rsp_t) == type(sub.rsp_t)) else $error("Parameter (man.rsp_t = %s) != (sub.rsp_t = %s)", $typename(man.rsp_t), $typename(sub.rsp_t));
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
