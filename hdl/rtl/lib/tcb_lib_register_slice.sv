////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library register slice request/response
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

module tcb_lib_register_slice #(
  // register slice parameters
  bit CFG_REQ_REG = 1'b1,  // register request  path
  bit CFG_RSP_REG = 1'b1   // register response path
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
    // bus widths
    if (sub.ABW != man.ABW)  $error("ERROR: %m parameter (sub.ABW = %d) != (man.ABW = %d)", sub.ABW, man.ABW);
    if (sub.DBW != man.DBW)  $error("ERROR: %m parameter (sub.DBW = %d) != (man.DBW = %d)", sub.DBW, man.DBW);
    if (sub.SLW != man.SLW)  $error("ERROR: %m parameter (sub.SLW = %d) != (man.SLW = %d)", sub.SLW, man.SLW);
    if (sub.BEW != man.BEW)  $error("ERROR: %m parameter (sub.BEW = %d) != (man.BEW = %d)", sub.BEW, man.BEW);
     // response delay
    if (sub.DLY != man.DLY + (CFG_REQ_REG ? 1 : 0) + (CFG_RSP_REG ? 1 : 0))
                             $error("ERROR: %m parameter (sub.DLY = %d) != (man.DLY = %d)", sub.DLY, man.DLY);
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

// TODO: this is certainly missing some complexity
generate
if (CFG_REQ_REG) begin: gen_req_reg

  // handshake
  always_ff @(posedge sub.clk, posedge sub.rst)
  if (sub.rst) begin
    man.vld <= 1'b0;
  end else begin
    man.vld <= sub.vld;
  end

  always_ff @(posedge sub.clk)
  begin
    // request optional
    man.inc = sub.inc;
    man.rpt = sub.rpt;
    man.lck = sub.lck;
    // request
    man.wen <= sub.wen;
    man.siz <= sub.siz;
    man.ben <= sub.ben;
    man.adr <= sub.adr;
    man.wdt <= sub.wdt;
  end

end: gen_req_reg
else begin: gen_req_cmb

  // handshake
  assign man.vld = sub.vld;
  // request optional
  assign man.inc = sub.inc;
  assign man.rpt = sub.rpt;
  assign man.lck = sub.lck;
  // request
  assign man.wen = sub.wen;
  assign man.siz = sub.siz;
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
    // response
    sub.rdt <= man.rdt;
    sub.err <= man.err;
  end

  // handshake
  assign sub.rdy = man.rdy;

end: gen_rsp_reg
else begin: gen_rsp_cmb

  // response
  assign sub.rdt = man.rdt;
  assign sub.err = man.err;
  assign sub.rdy = man.rdy;

end: gen_rsp_cmb
endgenerate

endmodule: tcb_lib_register_slice