////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) LIBrary ARBiter
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

module tcb_lib_arb #(
  // interconnect parameters
  int unsigned PN = 2,  // port number
  // arbitration priority mode
  string       MD = "FX",  // "FX" - fixed priority
                           // "RR" - round robin (TODO)
  // port priorities (lower number is higher priority)
  bit unsigned [PL-1:0] PRI [PN-1:0] = '{1'd1, 1'd0},
  localparam   PL = $clog2(PN)
)(
  // TCB interfaces
  tcb_if.sub tcb [PN-1:0],  // TCB subordinate ports (manager devices connect here)
  // control
  output logic [PL-1:0] sel   // select
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// report priority duplication
// TODO

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  logic [PN-1:0] vld;

  // extract valid from TCB
  generate
    for (genvar i=0; i<PN; i++) begin
      assign vld[i] = tcb[i].vld;
    end
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// fixed priority arbiter
////////////////////////////////////////////////////////////////////////////////

  // priority reorder
  function [PN-1:0] reorder (logic [PN-1:0] val);
    for (int unsigned i=0; i<PN; i++) begin
      assign reorder[i] = val[PRI[i]];
    end
  endfunction: reorder

  // priority encode
  function logic [PL-1:0] encode (logic [PN-1:0] val);
    encode = 'x;  // optimization of undefined encodings
    for (int i=PN; i>=0; i--) begin
      if (val[i])  encode = i[PL-1:0];
    end
  endfunction: encode

  // simple priority arbiter
  assign sel = PRI[encode(reorder(vld))];

endmodule: tcb_lib_arb
