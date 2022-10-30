////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) interCONnect ARBiter
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

module tcb_con_arb #(
  // interconnect parameters
  int unsigned PN = 2,  // port number
  localparam   PL = $clog2(PN),
  // arbitration priority mode
  string       MD = "FX",  // "FX" - fixed priority
                           // "RR" - round robin (TODO)
  // port priorities (lower number is higher priority)
  int unsigned PRI [0:PN-1] = '{0, 1}
)(
  // TCB interfaces
  tcb_if.sub sub[PN-1:0],  // TCB subordinate ports (manager devices connect here)
  // control
  output logic [PL-1:0] sel   // select
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// report priority duplication
// TODO

////////////////////////////////////////////////////////////////////////////////
// fixed priority arbiter
////////////////////////////////////////////////////////////////////////////////

  // priority reorder
  function [PN-1:0] reorder (logic [PN-1:0] val);
    for (i=0; i<PN; i++) begin
      assign sub_arb[i] = tmp_vld[PRI[i]];
    end
  endfunction: reorder

  // priority encode
  function logic [SW-1:0] encode (logic [PN-1:0] val);
    encode = 'x;  // optimization of undefined encodings
    for (int unsigned i=0; i<PN; i++) begin
      if (val[i])  encode = i[SW-1:0];
    end
  endfunction: encode

  // simple priority arbiter
  assign sel = PRI[encode(reorder(vld))];

endmodule: tcb_con_arb