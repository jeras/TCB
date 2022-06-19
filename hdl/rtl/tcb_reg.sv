////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus request/response register
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

module tcb_reg #(
  // bus parameters
  int unsigned AW = 32,    // address width
  int unsigned DW = 32,    // data width
  // TCB parameters
  bit          CFG_REQ_REG = 1'b1,  // register request  path
  bit          CFG_RSP_REG = 1'b1   // register response path
)(
  tcb_if.sub sub,  // TCB subordinate port (manager     device connects here)
  tcb_if.man man   // TCB manager     port (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// camparing subordinate and manager interface parameters
generate
  if (sub.DW  != man.DW )  $error("ERROR: %m parameter DW  validation failed");
  if (sub.DW  != man.DW )  $error("ERROR: %m parameter DW  validation failed");
  if (sub.SW  != man.SW )  $error("ERROR: %m parameter SW  validation failed");
  if (sub.DLY != man.DLY)  $error("ERROR: %m parameter DLY validation failed");
endgenerate

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

// TODO: this is certainly missing some complexity
generate
if (CFG_REQ_REG) begin: gen_req_reg

  always_ff @(posedge sub.clk, posedge sub.rst)
  if (sub.rst) begin
    man.vld <= 1'b0;
  end else begin
    man.vld <= sub.vld;
  end

  always_ff @(posedge sub.clk)
  begin
    man.wen <= sub.wen;
    man.ben <= sub.ben;
    man.adr <= sub.adr;
    man.wdt <= sub.wdt;
  end

end: gen_req_reg
else begin: gen_req_cmb

  assign man.vld = sub.vld;
  assign man.wen = sub.wen;
  assign man.ben = sub.ben;
  assign man.adr = sub.adr;
  assign man.wdt = sub.wdt;

end: gen_req_cmb
endgenerate

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

generate
if (CFG_RSP_REG) begin: gen_rsp_reg

  always_ff @(posedge man.clk)
  begin
    sub.rdt <= man.rdt;
    sub.err <= man.err;
  end

  assign sub.rdy = man.rdy;

end: gen_rsp_reg
else begin: gen_rsp_cmb

  assign sub.rdt = man.rdt;
  assign sub.err = man.err;
  assign sub.rdy = man.rdy;

end: gen_rsp_cmb
endgenerate

endmodule: tcb_reg