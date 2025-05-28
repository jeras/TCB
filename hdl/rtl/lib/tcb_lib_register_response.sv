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

module tcb_lib_register_response (
  tcb_if.sub sub,  // TCB subordinate interface (manager     device connects here)
  tcb_if.man man   // TCB manager     interface (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
  // comparing subordinate and manager interface parameters
  generate
  initial
  begin
    // parameters
    assert (man.HSK.DLY+1 == sub.HSK.DLY) else $error("Parameter (man.HSK.DLY+1 = %p+1) != (sub.HSK.DLY = %p)", man.HSK.DLY, sub.HSK.DLY);
    assert (man.BUS       == sub.BUS    ) else $error("Parameter (man.BUS       = %p  ) != (sub.BUS     = %p)", man.BUS    , sub.BUS    );
    assert (man.PCK       == sub.PCK    ) else $error("Parameter (man.PCK       = %p  ) != (sub.PCK     = %p)", man.PCK    , sub.PCK    );
    // request/response types
    // TODO: Questa is complaining here
//    assert (type(man.req_t) == type(sub.req_t)) else $error("Parameter (man.req_t = %s) != (sub.req_t = %s)", $typename(man.req_t), $typename(sub.req_t));
//    assert (type(man.rsp_t) == type(sub.rsp_t)) else $error("Parameter (man.rsp_t = %s) != (sub.rsp_t = %s)", $typename(man.rsp_t), $typename(sub.rsp_t));
  end
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// register response path
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;

  // request
  assign man.req = sub.req;

  // response
  always_ff @(posedge man.clk)
  begin
    // TODO: only on read enable, and byte enable (problem is what to do with LOG_SIZE
    sub.rsp <= man.rsp;
//    for (int unsigned i=0; i<man.BUS_BEN; i++) begin
//      if (man.dly[man.HSK.DLY].ben[i]) begin
//        sub.rsp.rdt[i] <= man.rsp.rdt[i];
//      end
//    end
//    // response status
//    sub.rsp.sts <= man.rsp.sts;
  end

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_register_response
