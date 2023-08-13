////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library arbiter
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

module tcb_lib_arbiter
  import tcb_pkg::*;
#(
  // arbitration priority mode
  parameter  string       MOD = "FX",  // "FX" - fixed priority, "RR" - round robin (TODO)
  // interconnect parameters (manager port number and logirthm)
  parameter  int unsigned MPN = 2,
  localparam int unsigned MPL = $clog2(MPN),
  // port priorities (lower number is higher priority)
  parameter  bit unsigned [MPL-1:0] PRI [MPN-1:0] = '{1'd1, 1'd0}
)(
  // TCB interfaces
  tcb_if.sub tcb [MPN-1:0],  // TCB subordinate ports (manager devices connect here)
  // control
  output logic [MPL-1:0] sel   // select
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// report priority duplication
// TODO

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  logic vld [MPN-1:0];

  // extract valid from TCB
  generate
    for (genvar i=0; i<MPN; i++) begin: map
      assign vld[i] = tcb[i].vld;
    end: map
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// fixed priority arbiter
////////////////////////////////////////////////////////////////////////////////

  typedef logic select_t [MPN-1:0];

  // priority reorder
  function automatic select_t reorder (
    logic                  val [MPN-1:0],  // input
    bit unsigned [MPL-1:0] ord [MPN-1:0]   // order
  );
    for (int unsigned i=0; i<MPN; i++) begin
      reorder[i] = val[ord[i]];
    end
  endfunction: reorder

  // priority encode
  function automatic logic [MPL-1:0] encode (select_t val);
    encode = 'x;  // optimization of undefined encodings
    for (int i=MPN; i>=0; i--) begin
      if (val[i])  encode = i[MPL-1:0];
    end
  endfunction: encode

  // priority arbiter
  assign sel = PRI[encode(reorder(vld, PRI))];

endmodule: tcb_lib_arbiter
