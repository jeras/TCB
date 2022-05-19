////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus subordinate
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
///////////////////////////////////////////////////////////////////////////////

module tcb_sub (
  // system bus
  tcb_if.sub bus
);

// response
task rsp (
  input  logic [bus.DW-1:0] rdt,     // read data
  input  logic              err,     // error
  input  int unsigned       dly = 0  // valid delay
);
  while (~bus.vld) begin
    @(posedge bus.clk);
  end
  repeat (dly)  @(posedge bus.clk);
  // read data
  bus.rdt <= rdt;
  bus.err <= err;
endtask: rsp

assign bus.rdy = 1'b1;

endmodule: tcb_sub