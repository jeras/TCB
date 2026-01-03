////////////////////////////////////////////////////////////////////////////////
// TCB lite (Tightly Coupled Bus) library multiplexer
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

module tcb_lite_lib_multiplexer #(
    // interconnect parameters (subordinate interface number and logarithm)
    parameter  int unsigned IFN = 2,
    localparam int unsigned IFL = $clog2(IFN)
)(
    // control
    input  logic [IFL-1:0] sel,  // select
    // TCB interfaces
    tcb_lite_if.sub sub[IFN-1:0],  // TCB subordinate interfaces (manager     devices connect here)
    tcb_lite_if.man man            // TCB manager     interface  (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
    // camparing subordinate and manager interface parameters
    generate
    for (genvar i=0; i<IFN; i++) begin: param
        initial begin
            assert (man.DELAY == sub[i].DELAY) else $error("Parameter (man.DELAY = %p) != (sub[%0d].DELAY = %p)", man.DELAY, i, sub[i].DELAY);
            assert (man.WIDTH == sub[i].WIDTH) else $error("Parameter (man.WIDTH = %p) != (sub[%0d].WIDTH = %p)", man.WIDTH, i, sub[i].WIDTH);
            assert (man.MASK  == sub[i].MASK ) else $error("Parameter (man.MASK  = %p) != (sub[%0d].MASK  = %p)", man.MASK , i, sub[i].MASK );
            assert (man.MODE  == sub[i].MODE ) else $error("Parameter (man.MODE  = %p) != (sub[%0d].MODE  = %p)", man.MODE , i, sub[i].MODE );
        end
    end: param
    endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // multiplexer select
    logic [IFL-1:0] sub_sel;
    logic [IFL-1:0] man_sel;

    // handshake
    logic                   vld [IFN-1:0];
    // request
    logic                   lck [IFN-1:0];  // arbitration lock
    logic                   wen [IFN-1:0];  // write enable (0-read, 1-write)
    logic [man.WIDTH  -1:0] adr [IFN-1:0];  // address
    logic [          2-1:0] siz [IFN-1:0];  // transfer size
    logic [man.WIDTH/8-1:0] byt [IFN-1:0];  // byte enable
    logic [man.WIDTH  -1:0] wdt [IFN-1:0];  // write data

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
        // handshake
        assign vld[i] = sub[i].vld;
        // request
        assign lck[i] = sub[i].lck;
        assign wen[i] = sub[i].wen;
        assign adr[i] = sub[i].adr;
        assign siz[i] = sub[i].siz;
        assign byt[i] = sub[i].byt;
        assign wdt[i] = sub[i].wdt;
    end: gen_req
    endgenerate

    // handshake multiplexer
    assign man.vld = vld[sub_sel];
    // request multiplexer
    assign man.lck = lck[sub_sel];
    assign man.wen = wen[sub_sel];
    assign man.adr = adr[sub_sel];
    assign man.siz = siz[sub_sel];
    assign man.byt = byt[sub_sel];
    assign man.wdt = wdt[sub_sel];

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

    // replicate response signals
    generate
    for (genvar i=0; i<IFN; i++) begin: gen_rsp
        // response
        assign sub[i].rdt = (man_sel == i[IFL-1:0]) ? man.rdt : 'x;
        assign sub[i].err = (man_sel == i[IFL-1:0]) ? man.err : 'x;
        // handshake
        assign sub[i].rdy = (sub_sel == i[IFL-1:0]) ? man.rdy : '0;
    end: gen_rsp
    endgenerate

endmodule: tcb_lite_lib_multiplexer
