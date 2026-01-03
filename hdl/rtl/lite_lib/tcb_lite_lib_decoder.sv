////////////////////////////////////////////////////////////////////////////////
// TCB lite (Tightly Coupled Bus) library decoder
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

module tcb_lite_lib_decoder #(
    // TCB parameters (contains address width)
    parameter  int unsigned WIDTH = 32,
    // interconnect parameters (subordinate interface number and logarithm)
    parameter  int unsigned IFN = 2,
    localparam int unsigned IFL = $clog2(IFN),
    // decoder address and mask array
    parameter  logic [WIDTH-1:0] MAP [IFN-1:0] = '{default: 'x}
)(
    // TCB interfaces
    tcb_lite_if.sub tcb,  // TCB subordinate interface (manager device connects here)
    // control
    output logic [IFL-1:0] sel  // select
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// report address range overlapping
// TODO

////////////////////////////////////////////////////////////////////////////////
// decoder
////////////////////////////////////////////////////////////////////////////////

    // match
    logic mch [IFN-1:0];

    // match
    generate
        for (genvar i=0; i<IFN; i++) begin
            assign mch[i] = tcb.adr ==? MAP[i];
        end
    endgenerate

    // encode
    function logic [IFL-1:0] encode (logic val [IFN-1:0]);
        encode = 'x;  // optimization of undefined encodings
        for (int i=IFN; i>=0; i--) begin
            if (val[i])  encode = i[IFL-1:0];
        end
    endfunction: encode

    // address decoder
    assign sel = encode(mch);

endmodule: tcb_lite_lib_decoder
