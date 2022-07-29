////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus arbiter
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

module tcb_arb #(
  // bus parameters
  int unsigned AW = 32,    // address width
  int unsigned DW = 32,    // data    width
  int unsigned BW = DW/8,  // byte e. width
  // interconnect parameters
  int unsigned PN = 2,     // port number
  // arbitration priority mode
  string       MD = "FX",  // "FX" - fixed priority
                           // "RR" - round robin (TODO)
  // port priorities (lower number is higher priority)
  int unsigned PRI [0:PN-1] = '{0, 1}
)(
  tcb_if.sub sub[PN-1:0],  // TCB subordinate ports (manager     devices connect here)
  tcb_if.man man           // TCB manager     port  (subordinate device connects here)
);

  genvar i;

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// camparing subordinate and manager interface parameters
generate
for (i=0; i<PN; i++) begin
  if (sub[i].AW  != man.AW )  $error("ERROR: %m parameter AW  validation failed");
  if (sub[i].DW  != man.DW )  $error("ERROR: %m parameter DW  validation failed");
  if (sub[i].SW  != man.SW )  $error("ERROR: %m parameter SW  validation failed");
  if (sub[i].DLY != man.DLY)  $error("ERROR: %m parameter DLY validation failed");
end
endgenerate

////////////////////////////////////////////////////////////////////////////////
// local parameters and functions
////////////////////////////////////////////////////////////////////////////////

// multiplexer select width
localparam SW = $clog2(PN);

// priority encoder
function [SW-1:0] clog2 (logic [PN-1:0] val);
  clog2 = 'x;  // optimization of undefined encodings
  for (int unsigned i=0; i<PN; i++) begin
    if (val[i])  clog2 = i[SW-1:0];
  end
endfunction: clog2

// report priority duplication
// TODO

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

// arbiter/multiplexer signals
logic [PN-1:0] sub_arb;
logic [SW-1:0] sub_sel;
logic [SW-1:0] man_sel;

logic          tmp_vld [PN-1:0];  // valid
logic          tmp_wen [PN-1:0];  // write enable
logic [AW-1:0] tmp_adr [PN-1:0];  // address
logic [BW-1:0] tmp_ben [PN-1:0];  // byte enable
logic [DW-1:0] tmp_wdt [PN-1:0];  // write data

////////////////////////////////////////////////////////////////////////////////
// arbiter
////////////////////////////////////////////////////////////////////////////////

// organize priority order
generate
for (i=0; i<PN; i++) begin: gen_arb
  assign sub_arb[i] = tmp_vld[PRI[i]];
end: gen_arb
endgenerate

// simple priority arbiter
assign sub_sel = PRI[clog2(sub_arb)];

// multiplexer integer select
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
  assign tmp_vld[i] = sub.vld[i];
  assign tmp_wen[i] = sub.wen[i];
  assign tmp_ben[i] = sub.ben[i];
  assign tmp_adr[i] = sub.adr[i];
  assign tmp_wdt[i] = sub.wdt[i];
end: gen_req
endgenerate

// multiplexer
assign man.vld = tmp_vld[sub_sel];
assign man.wen = tmp_wen[sub_sel];
assign man.ben = tmp_ben[sub_sel];
assign man.adr = tmp_adr[sub_sel];
assign man.wdt = tmp_wdt[sub_sel];

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

// replicate response signals
generate
for (i=0; i<PN; i++) begin: gen_rsp
  assign sub[i].rdt = (man_sel == i[SW-1:0]) ? man.rdt : 'x;  // response phase
  assign sub[i].err = (man_sel == i[SW-1:0]) ? man.err : 'x;  // response phase
  assign sub[i].rdy = (sub_sel == i[SW-1:0]) ? man.rdy : '0;  // request  phase
end: gen_rsp
endgenerate

endmodule: tcb_arb