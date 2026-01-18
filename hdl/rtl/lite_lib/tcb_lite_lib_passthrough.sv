////////////////////////////////////////////////////////////////////////////////
// TCB lite (Tightly Coupled Bus) library passthrough
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

module tcb_lite_lib_passthrough
    import tcb_lite_pkg::*;
(
    tcb_lite_if.sub sub,  // TCB subordinate interface (manager     device connects here)
    tcb_lite_if.man man   // TCB manager     interface (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
    // comparing subordinate and manager interface parameters
    initial
    begin
        assert (man.CFG == sub.CFG) else $error("Parameter (man.CFG = %p) != (sub.CFG = %p)", man.CFG, sub.CFG);
    end
`endif

////////////////////////////////////////////////////////////////////////////////
// passthrough
////////////////////////////////////////////////////////////////////////////////

    // handshake
    assign man.vld = sub.vld;
    assign sub.rdy = man.rdy;

    // request
    assign man.req.lck = sub.req.lck;
    assign man.req.ndn = sub.req.ndn;
    assign man.req.wen = sub.req.wen;
    assign man.req.ctl = sub.req.ctl;
    assign man.req.adr = sub.req.adr;
    assign man.req.siz = sub.req.siz;
    assign man.req.byt = sub.req.byt;
    assign man.req.wdt = sub.req.wdt;

    // response
    assign sub.rsp.rdt = man.rsp.rdt;
    assign sub.rsp.sts = man.rsp.sts;
    assign sub.rsp.err = man.rsp.err;

endmodule: tcb_lite_lib_passthrough
