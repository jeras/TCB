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

module tcb_lib_decoder
  import tcb_pkg::*;
#(
  // TCB parameters (contains address width)
  parameter  tcb_par_phy_t  PHY = TCB_PAR_PHY_DEF,
  // interconnect parameters (manager port number and logarithm)
  parameter  int unsigned MPN = 2,
  localparam int unsigned MPL = $clog2(MPN),
  // decoder address and mask array
  parameter  logic [PHY.ABW-1:0] DAM [MPN-1:0] = '{MPN{PHY.ABW'('x)}}
)(
  // TCB interfaces
  tcb_if.sub tcb,  // TCB subordinate port (manager device connects here)
  // select
  output logic [MPL-1:0] sel
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// report address range overlapping
// TODO

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  logic [PHY.ABW-1:0] adr;

  // extract address from TCB
  assign adr = tcb.req.adr;

////////////////////////////////////////////////////////////////////////////////
// decoder
////////////////////////////////////////////////////////////////////////////////

//  // match
//  function [MPN-1:0] match (
//    logic [PHY.ABW-1:0] val,           // input
//    logic [PHY.ABW-1:0] mch [MPN-1:0]   // matching reference
//  );
//    for (int unsigned i=0; i<MPN; i++) begin
//      assign match[i] = val ==? mch[i];
//    end
//  endfunction: match

  // match
  logic mch [MPN-1:0];

  // match
  generate
    for (genvar i=0; i<MPN; i++) begin
      assign mch[i] = adr ==? DAM[i];
    end
  endgenerate

  // encode
  function logic [MPL-1:0] encode (logic val [MPN-1:0]);
    encode = 'x;  // optimization of undefined encodings
    for (int i=MPN; i>=0; i--) begin
      if (val[i])  encode = i[MPL-1:0];
    end
  endfunction: encode

  // address decoder
//  assign sel = encode(match(adr, DAM));
  assign sel = encode(mch);

endmodule: tcb_lib_decoder
