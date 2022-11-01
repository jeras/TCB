////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) LIBrary MUltipleXer
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

module tcb_lib_mux #(
  // interconnect parameters
  int unsigned PN = 2,      // port number
  localparam   PL = $clog2(PN)
)(
  // control
  input  logic [PL-1:0] sel,  // select
  // TCB interfaces
  tcb_if.sub sub[PN-1:0],  // TCB subordinate ports (manager     devices connect here)
  tcb_if.man man           // TCB manager     port  (subordinate device connects here)
);

  genvar i;

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
  // camparing subordinate and manager interface parameters
  generate
  for (i=0; i<PN; i++) begin: param
    // bus widths
    if (sub[i].ABW != man.ABW)  $error("ERROR: %m parameter (sub[%d].ABW = %d) != (man.ABW = %d)", i, sub[i].ABW, man.ABW);
    if (sub[i].DBW != man.DBW)  $error("ERROR: %m parameter (sub[%d].DBW = %d) != (man.DBW = %d)", i, sub[i].DBW, man.DBW);
    if (sub[i].SLW != man.SLW)  $error("ERROR: %m parameter (sub[%d].SLW = %d) != (man.SLW = %d)", i, sub[i].SLW, man.SLW);
    if (sub[i].BEW != man.BEW)  $error("ERROR: %m parameter (sub[%d].BEW = %d) != (man.BEW = %d)", i, sub[i].BEW, man.BEW);
    // response delay
    if (sub[i].DLY != man.DLY)  $error("ERROR: %m parameter (sub[%d].DLY = %d) != (man.DLY = %d)", i, sub[i].DLY, man.DLY);
  end: param
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // multiplexer select
  logic [PL-1:0] sub_sel;
  logic [PL-1:0] man_sel;

  // handshake
  logic               tmp_vld [PN-1:0];  // valid
  // request
  logic               tmp_wen [PN-1:0];  // write enable
  logic [man.ABW-1:0] tmp_adr [PN-1:0];  // address
  logic [man.BEW-1:0] tmp_ben [PN-1:0];  // byte enable
  logic [man.DBW-1:0] tmp_wdt [PN-1:0];  // write data
  // request optional
  logic               tmp_lck [PN-1:0];  // arbitration lock
  logic               tmp_rpt [PN-1:0];  // repeat access

////////////////////////////////////////////////////////////////////////////////
// control
////////////////////////////////////////////////////////////////////////////////

  // subordinate (request) select
  assign sub_sel = sel;

  // multiplexer select
  always_ff @(posedge man.clk, posedge man.rst)
  if (man.rst) begin
    man_sel <= '0;
  end else if (man.trn) begin
    man_sel <= sub_sel;
  end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

  // organize request signals into indexable array
  // since a dynamix index can't be used on an array of interfaces
  generate
  for (i=0; i<PN; i++) begin: gen_req
    // handshake
    assign tmp_vld[i] = sub[i].vld;
    // request
    assign tmp_wen[i] = sub[i].wen;
    assign tmp_ben[i] = sub[i].ben;
    assign tmp_adr[i] = sub[i].adr;
    assign tmp_wdt[i] = sub[i].wdt;
    // request optional
    assign tmp_lck[i] = sub[i].lck;
    assign tmp_rpt[i] = sub[i].rpt;
  end: gen_req
  endgenerate

  // multiplexer
  // handshake
  assign man.vld = tmp_vld[sub_sel];
  // request
  assign man.wen = tmp_wen[sub_sel];
  assign man.ben = tmp_ben[sub_sel];
  assign man.adr = tmp_adr[sub_sel];
  assign man.wdt = tmp_wdt[sub_sel];
  // request optional
  assign man.lck = tmp_lck[sub_sel];
  assign man.rpt = tmp_rpt[sub_sel];

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // replicate response signals
  generate
  for (i=0; i<PN; i++) begin: gen_rsp
    // response
    assign sub[i].rdt = (man_sel == i[PL-1:0]) ? man.rdt : 'x;  // response phase
    assign sub[i].err = (man_sel == i[PL-1:0]) ? man.err : 'x;  // response phase
    // handshake
    assign sub[i].rdy = (sub_sel == i[PL-1:0]) ? man.rdy : '0;  // request  phase
  end: gen_rsp
  endgenerate

endmodule: tcb_lib_mux
