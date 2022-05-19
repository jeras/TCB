////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus manager
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

module tcb_man (
  // system bus
  tcb_if.man bus
);

initial bus.vld = 1'b0;

// request
task req (
  input  logic              wen,     // write enable
  input  logic [bus.AW-1:0] adr,     // address
  input  logic [bus.BW-1:0] ben,     // byte enable
  input  logic [bus.DW-1:0] wdt,     // write data
  input  int unsigned       dly = 0  // valid delay
);
  repeat (dly)  @(posedge bus.clk);
  bus.vld <= 1'b1;
  bus.wen <= wen;
  bus.adr <= adr;
  bus.ben <= ben;
  bus.wdt <= wdt;
  while (~bus.trn)  @(posedge bus.clk);
  // remove valid
  bus.vld <= 1'b0;
endtask: req

// response
task rsp (
  input  logic [bus.DW-1:0] rdt,     // read data
  input  logic              err      // error
);
  while (~bus.trn)  @(posedge bus.clk);
  // read data
  bus.rdt <= rdt;
  bus.err <= err;
endtask: rsp

endmodule: tcb_man