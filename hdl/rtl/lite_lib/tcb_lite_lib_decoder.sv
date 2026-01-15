////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library decoder
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

module tcb_lite_lib_decoder
    import tcb_lite_pkg::*;
#(
    // TCB parameters (contains address width)
    parameter  int unsigned ADR = 32,
    // interconnect parameters (subordinate interface number and logarithm)
    parameter  int unsigned IFN = 2,
    localparam int unsigned IFL = $clog2(IFN),
    // decoder address and mask array
    parameter  logic [ADR-1:0] DAM [IFN-1:0]
)(
    // TCB interfaces
    tcb_lite_if.mon mon,  // TCB subordinate interface (manager device connects here)
    // control
    output logic [IFL-1:0] sel  // select
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

// report address range overlapping
// TODO

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    logic [ADR-1:0] adr;

    // extract address from TCB
    assign adr = mon.req.adr;

////////////////////////////////////////////////////////////////////////////////
// decoder
////////////////////////////////////////////////////////////////////////////////

    // match
    logic mch [IFN-1:0];

    // match
    generate
        for (genvar i=0; i<IFN; i++) begin
            assign mch[i] = adr ==? DAM[i];
        end
    endgenerate

    // encode (convert from one-hot to binary encoding)
    function logic [IFL-1:0] encode (logic val [IFN-1:0]);
        encode = '0;
        for (int i=0; i<IFN; i++) begin
            encode |= val[i] ? i[IFL-1:0] : '0;
        end
    endfunction: encode

    // address decoder
    assign sel = encode(mch);

endmodule: tcb_lite_lib_decoder
