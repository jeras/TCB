////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library multiplexer
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

module tcb_lite_lib_multiplexer
    import tcb_lite_pkg::*;
#(
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
            assert (man.DLY == sub[i].DLY) else $error("Parameter (man.DLY = %p) != (sub[%0d].DLY = %p)", man.DLY, i, sub[i].DLY);
            assert (man.DAT == sub[i].DAT) else $error("Parameter (man.DAT = %p) != (sub[%0d].DAT = %p)", man.DAT, i, sub[i].DAT);
            assert (man.ADR == sub[i].ADR) else $error("Parameter (man.ADR = %p) != (sub[%0d].ADR = %p)", man.ADR, i, sub[i].ADR);
//            assert (man.MSK == sub[i].MSK) else $error("Parameter (man.MSK = %p) != (sub[%0d].MSK = %p)", man.MSK, i, sub[i].MSK);
            assert (man.MOD == sub[i].MOD) else $error("Parameter (man.MOD = %p) != (sub[%0d].MOD = %p)", man.MOD, i, sub[i].MOD);
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
    logic vld [IFN-1:0];

    // request
`ifdef SLANG
    logic               lck [IFN-1:0];
    logic               ndn [IFN-1:0];
    logic               wen [IFN-1:0];
    logic [man.CTL-1:0] ctl [IFN-1:0];
    logic [man.ADR-1:0] adr [IFN-1:0];
    logic [man.SIZ-1:0] siz [IFN-1:0];
    logic [man.BYT-1:0] byt [IFN-1:0];
    logic [man.DAT-1:0] wdt [IFN-1:0];
`else
    typedef man.req_t req_t;
    req_t req [IFN-1:0];
`endif

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
`ifdef SLANG
        assign lck[i] = sub[i].req.lck;
        assign ndn[i] = sub[i].req.ndn;
        assign wen[i] = sub[i].req.wen;
        assign ctl[i] = sub[i].req.ctl;
        assign adr[i] = sub[i].req.adr;
        assign siz[i] = sub[i].req.siz;
        assign byt[i] = sub[i].req.byt;
        assign wdt[i] = sub[i].req.wdt;
`else
        assign req[i] = sub[i].req;
`endif
    end: gen_req
    endgenerate

    // handshake multiplexer
    assign man.vld = vld[sub_sel];
    // request multiplexer
`ifdef SLANG
    assign man.req.lck = lck[sub_sel];
    assign man.req.ndn = ndn[sub_sel];
    assign man.req.wen = wen[sub_sel];
    assign man.req.ctl = ctl[sub_sel];
    assign man.req.adr = adr[sub_sel];
    assign man.req.siz = siz[sub_sel];
    assign man.req.byt = byt[sub_sel];
    assign man.req.wdt = wdt[sub_sel];
`else
    assign man.req = req[sub_sel];
`endif

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

    // replicate response signals
    generate
    for (genvar i=0; i<IFN; i++) begin: gen_rsp
        // response
`ifdef SLANG
        assign sub[i].rsp.rdt = (man_sel == i[IFL-1:0]) ? man.rsp.rdt : 'x;
        assign sub[i].rsp.sts = (man_sel == i[IFL-1:0]) ? man.rsp.sts : 'x;
        assign sub[i].rsp.err = (man_sel == i[IFL-1:0]) ? man.rsp.err : 'x;
`else
        assign sub[i].rsp = (man_sel == i[IFL-1:0]) ? man.rsp : '{default: 'x};
`endif
        // handshake
        assign sub[i].rdy = (sub_sel == i[IFL-1:0]) ? man.rdy : '0;
    end: gen_rsp
    endgenerate

endmodule: tcb_lite_lib_multiplexer
