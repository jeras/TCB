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
  // comparing subordinate and manager interface parameters
  generate
    // TODO
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// register response path
////////////////////////////////////////////////////////////////////////////////

  assign man.vld = sub.vld;  // handshake
  assign man.req = sub.req;  // request

  always_ff @(posedge man.clk)
  begin
    // TODO: only on read enable
    // data granularity
    for (int unsigned i=0; i<man.PHY_BEW; i+=man.PHY.SLW*GRN) begin
      if (man.rbe[man.PHY.DLY][i]) begin
        sub.rsp.rdt[i+:man.PHY.SLW*GRN] <= man.rsp.rdt[i+:man.PHY.SLW*GRN];
      end
    end
    // response status
    sub.rsp.sts <= man.rsp.sts;
  end

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_register_response
