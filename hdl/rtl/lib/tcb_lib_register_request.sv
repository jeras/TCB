////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library register slice for request path
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

module tcb_lib_register_request #(
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
    // TODO
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// register request path
////////////////////////////////////////////////////////////////////////////////

  // handshake
  always_ff @(posedge sub.clk, posedge sub.rst)
  if (sub.rst) begin
    man.vld <= 1'b0;
  end else begin
    if (sub.rdy) begin
      man.vld <= sub.vld;
    end
  end

  always_ff @(posedge sub.clk)
  begin
    man.req <= sub.req;
//    // data granularity
//    for (int unsigned i=0; i<sub.BEW; i+=sub.SLW*GRN) begin
//      if (sub.wen & sub.ben[i]) begin
//        man.wdt[i+:sub.SLW*GRN] <= sub.wdt[i+:sub.SLW*GRN];
//      end
//    end
  end

  // response
  assign sub.rsp = man.rsp;

  // handshake (valid is checked to avoid pipeline bubbles)
  assign sub.rdy = man.rdy | ~man.vld;

endmodule: tcb_lib_register_request
