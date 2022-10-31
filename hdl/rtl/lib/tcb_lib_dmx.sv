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
  int unsigned PN = 2,      // port number
  localparam   PL = $clog2(PN)
)(
  // control
  input  logic [PL-1:0] sel,  // select
  // TCB interfaces
  tcb_if.sub sub        ,  // TCB subordinate port  (manager     device connects here)
  tcb_if.man man[PN-1:0]   // TCB manager     ports (subordinate devices connect here)
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
    if (sub.AW  != man[i].AW )  $error("ERROR: %m parameter (sub.AW  = %d) != (man[%d].AW  = %d)", sub.AW , i, man[i].AW );
    if (sub.DW  != man[i].DW )  $error("ERROR: %m parameter (sub.DW  = %d) != (man[%d].DW  = %d)", sub.DW , i, man[i].DW );
    if (sub.SW  != man[i].SW )  $error("ERROR: %m parameter (sub.SW  = %d) != (man[%d].SW  = %d)", sub.SW , i, man[i].SW );
    if (sub.BW  != man[i].BW )  $error("ERROR: %m parameter (sub.BW  = %d) != (man[%d].BW  = %d)", sub.BW , i, man[i].BW );
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
  for (i=0; i<PN; i++) begin: gen_req
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
  for (i=0; i<PN; i++) begin: gen_rsp
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
