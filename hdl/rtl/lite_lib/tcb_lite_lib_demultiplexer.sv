////////////////////////////////////////////////////////////////////////////////
// TCB lite (Tightly Coupled Bus) library demultiplexer
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

module tcb_lite_lib_demultiplexer #(
    // interconnect parameters (manager interface number and logarithm)
    parameter  int unsigned IFN = 2,
    localparam int unsigned IFL = $clog2(IFN)
)(
    // control
    input  logic [IFL-1:0] sel,  // select
    // TCB interfaces
    tcb_lite_if.sub sub         ,  // TCB subordinate interface  (manager     device connects here)
    tcb_lite_if.man man[IFN-1:0]   // TCB manager     interfaces (subordinate devices connect here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
    // comparing subordinate and manager interface parameters
    generate
    for (genvar i=0; i<IFN; i++) begin: param
        initial begin    
            assert (man[i].DELAY == sub.DELAY) else $error("Parameter (man[%0d].DELAY = %p) != (sub.DELAY = %p)", i, man[i].DELAY, sub.DELAY);
            assert (man[i].WIDTH == sub.WIDTH) else $error("Parameter (man[%0d].WIDTH = %p) != (sub.WIDTH = %p)", i, man[i].WIDTH, sub.WIDTH);
            assert (man[i].MASK  == sub.MASK ) else $error("Parameter (man[%0d].MASK  = %p) != (sub.MASK  = %p)", i, man[i].MASK , sub.MASK );
            assert (man[i].MODE  == sub.MODE ) else $error("Parameter (man[%0d].MODE  = %p) != (sub.MODE  = %p)", i, man[i].MODE , sub.MODE );
        end
    end: param
    endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // demultiplexer signals
    logic [IFL-1:0] sub_sel;
    logic [IFL-1:0] man_sel;
    
    // response
    logic [sub.WIDTH  -1:0] rdt [IFN-1:0];  // read data
    logic                   err [IFN-1:0];  // bus error
    // handshake
    logic                   rdy [IFN-1:0];

////////////////////////////////////////////////////////////////////////////////
// control
////////////////////////////////////////////////////////////////////////////////

    // select
    assign sub_sel = sel;

    // demultiplexer select
    always_ff @(posedge sub.clk, posedge sub.rst)
    if (sub.rst) begin
        man_sel <= '0;
    end else if (sub.trn) begin
        man_sel <= sub_sel;
    end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

    // replicate request signals
    generate
    for (genvar i=0; i<IFN; i++) begin: gen_req
        // handshake
        assign man[i].vld = (sub_sel == i) ? sub.vld : 1'b0;
        // request
        assign man[i].lck = (sub_sel == i) ? sub.lck :   'x;
        assign man[i].wen = (sub_sel == i) ? sub.wen :   'x;
        assign man[i].adr = (sub_sel == i) ? sub.adr :   'x;
        assign man[i].siz = (sub_sel == i) ? sub.siz :   'x;
        assign man[i].byt = (sub_sel == i) ? sub.byt :   'x;
        assign man[i].wdt = (sub_sel == i) ? sub.wdt :   'x;
    end: gen_req
    endgenerate

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

    // organize response signals into indexable array
    // since a dynamic index can't be used on an array of interfaces
    generate
    for (genvar i=0; i<IFN; i++) begin: gen_rsp
        // response
        assign rdt[i] = man[i].rdt;
        assign err[i] = man[i].err;
        // handshake
        assign rdy[i] = man[i].rdy;
    end: gen_rsp
    endgenerate

    // response multiplexer
    assign sub.rdt = rdt[man_sel];
    assign sub.err = err[man_sel];
    // handshake multiplexer
    assign sub.rdy = rdy[sub_sel];

endmodule: tcb_lite_lib_demultiplexer
