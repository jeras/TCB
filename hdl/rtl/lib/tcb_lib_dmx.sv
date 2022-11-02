////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) LIBrary DeMultipleXer
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

module tcb_lib_dmx #(
  // bus widths
  int unsigned AW = 32,     // address     width
  int unsigned DW = 32,     // data        width
  int unsigned SW =     8,  // selection   width
  int unsigned BW = DW/SW,  // byte enable width
  // response delay
  int unsigned DLY = 1,
  // interconnect parameters
  parameter  int unsigned PN = 2,      // port number
  localparam int unsigned PL = $clog2(PN)
)(
  // control
  input  logic [PL-1:0] sel,  // select
  // TCB interfaces
  tcb_if.sub sub        ,  // TCB subordinate port  (manager     device connects here)
  tcb_if.man man[PN-1:0]   // TCB manager     ports (subordinate devices connect here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
  // camparing subordinate and manager interface parameters
  generate
  for (genvar i=0; i<PN; i++) begin: param
    // bus widths
    if (sub.ABW != man[i].ABW)  $error("ERROR: %m parameter (sub.ABW = %d) != (man[%d].ABW = %d)", sub.ABW, i, man[i].ABW);
    if (sub.DBW != man[i].DBW)  $error("ERROR: %m parameter (sub.DBW = %d) != (man[%d].DBW = %d)", sub.DBW, i, man[i].DBW);
    if (sub.SLW != man[i].SLW)  $error("ERROR: %m parameter (sub.SLW = %d) != (man[%d].SLW = %d)", sub.SLW, i, man[i].SLW);
    if (sub.BEW != man[i].BEW)  $error("ERROR: %m parameter (sub.BEW = %d) != (man[%d].BEW = %d)", sub.BEW, i, man[i].BEW);
    // response delay
    if (sub.DLY != man[i].DLY)  $error("ERROR: %m parameter (sub.DLY = %d) != (man[%d].DLY = %d)", sub.DLY, i, man[i].DLY);
  end: param
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // demultiplexer signals
  logic [PL-1:0] sub_sel;
  logic [PL-1:0] man_sel;

  // response
  logic [DW-1:0] tmp_rdt [PN-1:0];  // read data
  logic          tmp_err [PN-1:0];  // error
  // handshake
  logic          tmp_rdy [PN-1:0];  // acknowledge

////////////////////////////////////////////////////////////////////////////////
// control
////////////////////////////////////////////////////////////////////////////////

  // select
  assign sub_sel = sel;

  // demultiplexer select
  always_ff @(posedge sub.clk, posedge sub.rst)
  if (sub.rst) begin
    man_sel <= '0;
  end else if (sub.trn) begin
    man_sel <= sub_sel;
  end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

  // replicate request signals
  generate
  for (genvar i=0; i<PN; i++) begin: gen_req
    // handshake
    assign man[i].vld = (sub_sel == i) ? sub.vld : '0;
    // request
    assign man[i].wen = (sub_sel == i) ? sub.wen : 'x;
    assign man[i].ben = (sub_sel == i) ? sub.ben : 'x;
    assign man[i].adr = (sub_sel == i) ? sub.adr : 'x;
    assign man[i].wdt = (sub_sel == i) ? sub.wdt : 'x;
    // request optional
    assign man[i].lck = (sub_sel == i) ? sub.lck : 'x;
    assign man[i].rpt = (sub_sel == i) ? sub.rpt : 'x;
  end: gen_req
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // organize response signals into indexable array
  // since a dynamic index can't be used on an array of interfaces
  generate
  for (genvar i=0; i<PN; i++) begin: gen_rsp
    // response
    assign tmp_rdt[i] = man[i].rdt;
    assign tmp_err[i] = man[i].err;
    // handshake
    assign tmp_rdy[i] = man[i].rdy;
  end: gen_rsp
  endgenerate

  // multiplexer
  // response
  assign sub.rdt = tmp_rdt[man_sel];  // response phase
  assign sub.err = tmp_err[man_sel];  // response phase
  // handskake
  assign sub.rdy = tmp_rdy[sub_sel];  // request  phase

endmodule: tcb_lib_dmx
