////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library demultiplexer
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
            assert (man[i].DLY == sub.DLY) else $error("Parameter (man[%0d].DLY = %p) != (sub.DLY = %p)", i, man[i].DLY, sub.DLY);
            assert (man[i].DAT == sub.DAT) else $error("Parameter (man[%0d].DAT = %p) != (sub.DAT = %p)", i, man[i].DAT, sub.DAT);
            assert (man[i].ADR == sub.ADR) else $error("Parameter (man[%0d].ADR = %p) != (sub.ADR = %p)", i, man[i].ADR, sub.ADR);
            assert (man[i].MSK == sub.MSK) else $error("Parameter (man[%0d].MSK = %p) != (sub.MSK = %p)", i, man[i].MSK, sub.MSK);
            assert (man[i].MOD == sub.MOD) else $error("Parameter (man[%0d].MOD = %p) != (sub.MOD = %p)", i, man[i].MOD, sub.MOD);
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
`ifdef SLANG
    logic [sub.DAT-1:0] rdt [IFN-1:0];  // read data
    logic               err [IFN-1:0];  // bus error
`else
    typedef sub.rsp_t rsp_t;
    rsp_t rsp [IFN-1:0];
`endif
    // handshake
    logic rdy [IFN-1:0];

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
`ifdef SLANG
        assign man[i].req.lck = (sub_sel == i) ? sub.req.lck : 'x;
        assign man[i].req.ndn = (sub_sel == i) ? sub.req.ndn : 'x;
        assign man[i].req.wen = (sub_sel == i) ? sub.req.wen : 'x;
        assign man[i].req.adr = (sub_sel == i) ? sub.req.adr : 'x;
        assign man[i].req.siz = (sub_sel == i) ? sub.req.siz : 'x;
        assign man[i].req.byt = (sub_sel == i) ? sub.req.byt : 'x;
        assign man[i].req.wdt = (sub_sel == i) ? sub.req.wdt : 'x;
`else
        assign man[i].req = (sub_sel == i) ? sub.req : '{default: 'x};
`endif

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
`ifdef SLANG
        assign rdt[i] = man[i].rsp.rdt;
        assign err[i] = man[i].rsp.err;
`else
        assign rsp[i] = man[i].rsp;
`endif
        // handshake
        assign rdy[i] = man[i].rdy;
    end: gen_rsp
    endgenerate

    // response multiplexer
`ifdef SLANG
    assign sub.rsp.rdt = rdt[man_sel];
    assign sub.rsp.err = err[man_sel];
`else
    assign sub.rsp = rsp[man_sel];
`endif
    // handshake multiplexer
    assign sub.rdy = rdy[sub_sel];

endmodule: tcb_lite_lib_demultiplexer
