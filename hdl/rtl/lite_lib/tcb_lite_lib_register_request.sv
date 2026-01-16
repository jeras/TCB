////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library register slice for request path
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

module tcb_lite_lib_register_request
    import tcb_lite_pkg::*;
#(
    parameter string OPT = "POWER"  // optimization for "POWER" or "COMPLEXITY"
)(
    tcb_lite_if.sub sub,  // TCB subordinate interface (manager     device connects here)
    tcb_lite_if.man man   // TCB manager     interface (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
    // comparing subordinate and manager interface parameters
    initial
    begin
        assert (man.DLY+1 == sub.DLY) else $error("Parameter (man.DLY = %p)+1 != (sub.DLY = %p)", man.DLY, sub.DLY);

        assert (man.DAT == sub.DAT) else $error("Parameter (man.DAT = %p) != (sub.DAT = %p)", man.DAT, sub.DAT);
        assert (man.ADR == sub.ADR) else $error("Parameter (man.ADR = %p) != (sub.ADR = %p)", man.ADR, sub.ADR);
//        assert (man.MSK == sub.MSK) else $error("Parameter (man.MSK = %p) != (sub.MSK = %p)", man.MSK, sub.MSK);
        assert (man.MOD == sub.MOD) else $error("Parameter (man.MOD = %p) != (sub.MOD = %p)", man.MOD, sub.MOD);
    end
`endif

////////////////////////////////////////////////////////////////////////////////
// register request path
////////////////////////////////////////////////////////////////////////////////

    // handshake
    always_ff @(posedge sub.clk, posedge sub.rst)
    if (sub.rst) begin
        man.vld <= 1'b0;
    end else begin
        if (sub.rdy) begin
            man.vld <= sub.vld;
        end
    end

    // request
    always_ff @(posedge sub.clk)
    if (sub.trn) begin
        man.req.lck <= sub.req.lck;
        man.req.ndn <= sub.req.ndn;
        man.req.wen <= sub.req.wen;
        man.req.adr <= sub.req.adr;
        man.req.ctl <= sub.req.ctl;
    end

    generate
    case (sub.MOD)
        1'b0: begin: byt
            // logarithmic size
            always_ff @(posedge sub.clk)
            if (sub.trn)  man.req.siz <= sub.req.siz;
            // write data
            for (genvar i=0; i<sub.BYT; i++) begin: wdt
                always_ff @(posedge sub.clk)
                if (sub.trn & sub.req.wen & (i < 2**sub.req.siz   ))  man.req.wdt[i*8+:8] <= sub.req.wdt[i*8+:8];
            end: wdt
        end: byt
        1'b1: begin: byt
            // byte enable
            always_ff @(posedge sub.clk)
            if (sub.trn)  man.req.byt <= sub.req.byt;
            // write data
            for (genvar i=0; i<sub.BYT; i++) begin: wdt
                always_ff @(posedge sub.clk)
                if (sub.trn & sub.req.wen & (       sub.req.byt[i]))  man.req.wdt[i*8+:8] <= sub.req.wdt[i*8+:8];
            end: wdt
        end: byt
    endcase
    endgenerate

    // response
`ifdef SLANG
    assign sub.rsp.rdt = man.rsp.rdt;
    assign sub.rsp.sts = man.rsp.sts;
    assign sub.rsp.err = man.rsp.err;
`else
    assign sub.rsp = man.rsp;
`endif

    // handshake (valid is checked to avoid pipeline bubbles)
    assign sub.rdy = man.rdy | ~man.vld;

endmodule: tcb_lite_lib_register_request
