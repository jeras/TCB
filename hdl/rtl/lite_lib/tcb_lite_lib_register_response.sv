////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library register slice for response path
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

module tcb_lite_lib_register_response
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
        assert (man.MSK == sub.MSK) else $error("Parameter (man.MSK = %p) != (sub.MSK = %p)", man.MSK, sub.MSK);
        assert (man.MOD == sub.MOD) else $error("Parameter (man.MOD = %p) != (sub.MOD = %p)", man.MOD, sub.MOD);
    end
`endif

////////////////////////////////////////////////////////////////////////////////
// register response path
////////////////////////////////////////////////////////////////////////////////

    // handshake
    assign man.vld = sub.vld;

    // request
`ifdef SLANG
    assign man.req.lck = sub.req.lck;
    assign man.req.ndn = sub.req.ndn;
    assign man.req.wen = sub.req.wen;
    assign man.req.adr = sub.req.adr;
    assign man.req.siz = sub.req.siz;
    assign man.req.byt = sub.req.byt;
    assign man.req.wdt = sub.req.wdt;
`else
    assign man.req = sub.req;
`endif

    // response (data)
    generate
    case (sub.MOD)
        1'b0: begin: byt
            // read data (logarithmic size)
        // TODO: only on read enable, and byte enable (problem is what to do with LOG_SIZE
            for (genvar i=0; i<sub.BYT; i++) begin: rdt
                always_ff @(posedge man.clk)
                if (man.trn_dly[man.DLY] & ~sub.req.wen & (i < 2**sub.req.siz   ))  sub.rsp.rdt[i*8+:8] <= man.rsp.rdt[i*8+:8];
            end: rdt
        end: byt
        1'b1: begin: byt
            // read data (byte enable)
            for (genvar i=0; i<sub.BYT; i++) begin: rdt
                always_ff @(posedge man.clk)
                if (man.trn_dly[man.DLY] & ~sub.req.wen & (       sub.req.byt[i]))  sub.rsp.rdt[i*8+:8] <= man.rsp.rdt[i*8+:8];
            end: rdt
        end: byt
    endcase
    endgenerate

    // response (error)
    always_ff @(posedge man.clk)
    begin
        if (man.trn_dly[man.DLY]) begin
            sub.rsp.err <= man.rsp.err;
        end
    end

    // handshake
    assign sub.rdy = man.rdy;

endmodule: tcb_lite_lib_register_response
