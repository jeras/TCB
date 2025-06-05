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
    assert (man.HSK.DLY == sub.HSK.DLY) else $error("Parameter (man.HSK.DLY = %p) != (sub.HSK.DLY = %p)", man.HSK.DLY, sub.HSK.DLY);
    assert (man.BUS     == sub.BUS    ) else $error("Parameter (man.BUS     = %p) != (sub.BUS     = %p)", man.BUS    , sub.BUS    );
    assert (man.PMA     == sub.PMA    ) else $error("Parameter (man.PMA     = %p) != (sub.PMA     = %p)", man.PMA    , sub.PMA    );
    // request/response types
    // TODO: Questa is complaining here
//    assert (type(man.req_t) == type(sub.req_t)) else $error("Parameter (man.req_t = %s) != (sub.req_t = %s)", $typename(man.req_t), $typename(sub.req_t));
//    assert (type(man.rsp_t) == type(sub.rsp_t)) else $error("Parameter (man.rsp_t = %s) != (sub.rsp_t = %s)", $typename(man.rsp_t), $typename(sub.rsp_t));
  end
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// register backpressure path
////////////////////////////////////////////////////////////////////////////////

  // request temporary buffer
  // TODO: test different approaches
  //sub.req_t tmp;
  //type(sub.req) tmp;
  tcb_req_t tmp;

  // handshake
  assign man.vld = sub.rdy ? sub.vld : 1'b1;

  // request
  always_ff @(posedge sub.clk)
  begin
    if (sub.vld & sub.rdy & ~man.rdy) begin
      tmp <= sub.req;
//      // TODO: handle only enabled data bytes
//      for (int unsigned i=0; i<sub.BUS_BYT; i++) begin
//        // data granularity
//        if (sub.req.wen & sub.req.byt[i]) begin
//          tmp.wdt[i] <= sub.req.wdt[i];
//        end
//      end
    end
  end

  // request
  assign man.req = sub.rdy ? sub.req : tmp;

  // response
  assign sub.rsp = man.rsp;

  // handshake
  always_ff @(posedge sub.clk, posedge sub.rst)
  if (sub.rst) begin
    sub.rdy <= 1'b1;
  end else begin
    if (sub.rdy)  sub.rdy <= ~(sub.vld & ~man.rdy);
    else          sub.rdy <=              man.rdy ;
  end

endmodule: tcb_lib_register_backpressure
