////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) interCONnect ERRor subordinate
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

module tcb_con_err #(
  // response delay
  int unsigned DLY = 1
)(
  // system bus interface
  tcb_if.sub bus
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
generate
  if (DLY != bus.DLY)  $error("ERROR: %m parameter DLY validation failed");
endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// TCB access
////////////////////////////////////////////////////////////////////////////////

// response is immediate
assign bus.rdy = 1'b1;

// data is don't care
assign bus.rdt = 'x;

// the response is always an error
assign bus.err = 1'b1;

endmodule: tcb_con_err