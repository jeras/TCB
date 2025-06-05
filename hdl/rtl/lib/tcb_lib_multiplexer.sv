////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library multiplexer
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

module tcb_lib_multiplexer
  import tcb_pkg::*;
#(
  // interconnect parameters (subordinate interface number and logarithm)
  parameter  int unsigned IFN = 2,
  localparam int unsigned IFL = $clog2(IFN)
)(
  // control
  input  logic [IFL-1:0] sel,  // select
  // TCB interfaces
  tcb_if.sub sub[IFN-1:0],  // TCB subordinate interfaces (manager     devices connect here)
  tcb_if.man man            // TCB manager     interface  (subordinate device connects here)
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

  // multiplexer select
  logic [IFL-1:0] sub_sel;
  logic [IFL-1:0] man_sel;

//  // TODO: remove once simulators support access to types inside interfaces
//  // request
//  typedef struct packed {
//    tcb_req_cmd_def_t       cmd;  // command (optional)
//    logic                   wen;  // write enable
//    logic                   ren;  // write enable
//    logic                   ndn;  // endianness
//    logic [man.BUS.ADR-1:0] adr;  // address
//    logic [man.BUS_SIZ-1:0] siz;  // transfer size
//    logic [man.BUS_BYT-1:0] ben;  // byte enable
//    logic [man.BUS.DAT-1:0] wdt;  // write data
//  } man_req_t;

  typedef man.req_t man_req_t;

  logic           tmp_vld [IFN-1:0];  // handshake
  man_req_t       tmp_req [IFN-1:0];  // request

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
  for (genvar i=0; i<IFN; i++) begin: gen_req
    assign tmp_vld[i] = sub[i].vld;  // handshake
    assign tmp_req[i] = sub[i].req;  // request
  end: gen_req
  endgenerate

  // multiplexer
  assign man.vld = tmp_vld[sub_sel];  // handshake
  assign man.req = tmp_req[sub_sel];  // request

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // replicate response signals
  generate
  for (genvar i=0; i<IFN; i++) begin: gen_rsp
    assign sub[i].rsp = (man_sel == i[IFL-1:0]) ? man.rsp : 'x;  // response
    assign sub[i].rdy = (sub_sel == i[IFL-1:0]) ? man.rdy : '0;  // handshake
  end: gen_rsp
  endgenerate

endmodule: tcb_lib_multiplexer
