////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) interCONnect DECoder
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

module tcb_con_dec #(
  // bus parameters
  int unsigned AW = 32,    // address width
  // interconnect parameters
  int unsigned PN = 2,     // port number
  localparam   PL = $clog2(PN),
  // decoder addresses and masks
  logic [PN-1:0] [AW-1:0] AS = PN'('x)
)(
  // TCB interfaces
  tcb_if.sub sub,  // TCB subordinate port (manager device connects here)
  // control
  output logic [PL-1:0] sel   // select
);

  genvar i;

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// report address range overlapping
// TODO

////////////////////////////////////////////////////////////////////////////////
// decoder
////////////////////////////////////////////////////////////////////////////////

  // priority encoder
  function [SW-1:0] clog2 (logic [PN-1:0] val);
    clog2 = 'x;  // optimization of undefined encodings
    for (int unsigned i=0; i<PN; i++) begin
      if (val[i])  clog2 = i[SW-1:0];
    end
  endfunction: clog2

  // address range decoder into one hot vector
  generate
  for (i=0; i<PN; i++) begin: gen_dec
    assign sub_dec[i] = sub.adr ==? AS[i];
  end: gen_dec
  endgenerate

  // priority encoder
  assign sel = clog2(sub_dec);

endmodule: tcb_con_dec