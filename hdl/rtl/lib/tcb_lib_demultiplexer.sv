////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library demultiplexer
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

module tcb_lib_demultiplexer
  import tcb_pkg::*;
#(
  // interconnect parameters (manager interface number and logarithm)
  parameter  int unsigned IFN = 2,
  localparam int unsigned IFL = $clog2(IFN)
)(
  // control
  input  logic [IFL-1:0] sel,  // select
  // TCB interfaces
  tcb_if.sub sub         ,  // TCB subordinate interface  (manager     device connects here)
  tcb_if.man man[IFN-1:0]   // TCB manager     interfaces (subordinate devices connect here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
  // camparing subordinate and manager interface parameters
  generate
  for (genvar i=0; i<IFN; i++) begin: param
    // TODO
  end: param
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // demultiplexer signals
  logic [IFL-1:0] sub_sel;
  logic [IFL-1:0] man_sel;

//  // TODO: remove once simulators support access to types inside interfaces
//  // response
//  typedef struct packed {
//    logic [sub.BUS.DAT-1:0] rdt;  // read data
//    tcb_rsp_sts_t           sts;  // status (optional)
//  } sub_rsp_t;

  typedef sub.rsp_t sub_rsp_t;

  sub_rsp_t       tmp_rsp [IFN-1:0];  // response
  logic           tmp_rdy [IFN-1:0];  // handshake

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
  for (genvar i=0; i<IFN; i++) begin: gen_req
    assign man[i].vld = (sub_sel == i) ? sub.vld : 1'b0;  // handshake
    assign man[i].req = (sub_sel == i) ? sub.req :   'x;  // request
  end: gen_req
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // organize response signals into indexable array
  // since a dynamic index can't be used on an array of interfaces
  generate
  for (genvar i=0; i<IFN; i++) begin: gen_rsp
    assign tmp_rsp[i] = man[i].rsp;  // response
    assign tmp_rdy[i] = man[i].rdy;  // handshake
  end: gen_rsp
  endgenerate

  // multiplexer
  assign sub.rsp = tmp_rsp[man_sel];  // response
  assign sub.rdy = tmp_rdy[sub_sel];  // handskake

endmodule: tcb_lib_demultiplexer
