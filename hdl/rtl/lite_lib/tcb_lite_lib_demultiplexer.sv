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

module tcb_lite_lib_demultiplexer
    import tcb_lite_pkg::*;
#(
    // interconnect parameters (manager interface number and logarithm)
    parameter  int unsigned IFN = 2,
    localparam int unsigned IFL = $clog2(IFN)
)(
    // control
    input  logic [IFL-1:0] sel,  // select
    // TCB-Lite interfaces
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
            assert (man[i].CFG == sub.CFG) else $error("Parameter (man[%0d].CFG = %p) != (sub.CFG = %p)", i, man[i].CFG, sub.CFG);
        end
    end: param
    endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // demultiplexer signals
    logic [IFL-1:0] req_sel;
    logic [IFL-1:0] rsp_sel;
    
    // response
    logic [sub.CFG.BUS.DAT-1:0] rdt [IFN-1:0];  // read data
    logic [sub.CFG.BUS.STS-1:0] sts [IFN-1:0];  // status
    logic                       err [IFN-1:0];  // bus error

    // handshake
    logic rdy [IFN-1:0];

////////////////////////////////////////////////////////////////////////////////
// control
////////////////////////////////////////////////////////////////////////////////

    // TODO: this code only works with DLY=1

    // request select
    assign req_sel = sel;

    // response select
    generate
    if (sub.CFG.HSK.DLY == 0) begin
        assign rsp_sel = req_sel;
    end
    else if (sub.CFG.HSK.DLY == 1) begin
        always_ff @(posedge sub.clk, posedge sub.rst)
        if (sub.rst) begin
            rsp_sel <= '0;
        end else if (sub.trn) begin
            rsp_sel <= req_sel;
        end
    end
    else begin
        // TODO
        initial $error("only DLY 0/1 are supported, TODO");
    end
    endgenerate
    

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

    // replicate request signals
    generate
    for (genvar i=0; i<IFN; i++) begin: gen_req
        // handshake
        assign man[i].vld = (req_sel == i) ? sub.vld : 1'b0;
        // request
        assign man[i].req.lck = (req_sel == i[IFL-1:0]) ? sub.req.lck : 'x;
        assign man[i].req.ndn = (req_sel == i[IFL-1:0]) ? sub.req.ndn : 'x;
        assign man[i].req.wen = (req_sel == i[IFL-1:0]) ? sub.req.wen : 'x;
        assign man[i].req.ren = (req_sel == i[IFL-1:0]) ? sub.req.ren : 'x;
        assign man[i].req.ctl = (req_sel == i[IFL-1:0]) ? sub.req.ctl : 'x;
        assign man[i].req.adr = (req_sel == i[IFL-1:0]) ? sub.req.adr : 'x;
        assign man[i].req.siz = (req_sel == i[IFL-1:0]) ? sub.req.siz : 'x;
        assign man[i].req.byt = (req_sel == i[IFL-1:0]) ? sub.req.byt : 'x;
        assign man[i].req.wdt = (req_sel == i[IFL-1:0]) ? sub.req.wdt : 'x;
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
        assign rdt[i] = man[i].rsp.rdt;
        assign sts[i] = man[i].rsp.sts;
        assign err[i] = man[i].rsp.err;
        // handshake
        assign rdy[i] = man[i].rdy;
    end: gen_rsp
    endgenerate

    // response multiplexer
    assign sub.rsp.rdt = rdt[rsp_sel];
    assign sub.rsp.sts = sts[rsp_sel];
    assign sub.rsp.err = err[rsp_sel];

    // handshake multiplexer
    assign sub.rdy = rdy[req_sel];

endmodule: tcb_lite_lib_demultiplexer
