////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library decoder
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

module tcb_lib_decoder #(
  // TCB parameters
  parameter  int unsigned ABW = 32,   // address width
  // interconnect parameters
  parameter  int unsigned PN = 2,     // port number
  localparam int unsigned PL = $clog2(PN),
  // decoder address and mask array
  parameter  logic [ABW-1:0] DAM [PN-1:0] = '{PN{ABW'('x)}}
)(
  // TCB interfaces
  tcb_if.sub tcb,  // TCB subordinate port (manager device connects here)
  // control
  output logic [PL-1:0] sel   // select
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// report address range overlapping
// TODO

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  logic [ABW-1:0] adr;

  // extract address from TCB
  assign adr = tcb.adr;

////////////////////////////////////////////////////////////////////////////////
// decoder
////////////////////////////////////////////////////////////////////////////////

//  // match
//  function [PN-1:0] match (
//    logic [ABW-1:0] val,           // input
//    logic [ABW-1:0] mch [PN-1:0]   // matching reference
//  );
//    for (int unsigned i=0; i<PN; i++) begin
//      assign match[i] = val ==? mch[i];
//    end
//  endfunction: match

  logic mch [PN-1:0];
  // match
  generate
    for (genvar i=0; i<PN; i++) begin
      assign mch[i] = adr ==? DAM[i];
    end
  endgenerate

  // encode
  function logic [PL-1:0] encode (logic val [PN-1:0]);
    encode = 'x;  // optimization of undefined encodings
    for (int i=PN; i>=0; i--) begin
      if (val[i])  encode = i[PL-1:0];
    end
  endfunction: encode

  // address decoder
//  assign sel = encode(match(adr, DAM));
  assign sel = encode(mch);

endmodule: tcb_lib_decoder