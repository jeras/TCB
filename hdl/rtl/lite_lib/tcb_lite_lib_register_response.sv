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
    // TCB-Lite interfaces
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
        assert (man.CFG.HSK.DLY+1 == sub.CFG.HSK.DLY) else $error("Parameter (man.CFG.HSK.DLY = %p)+1 != (sub.CFG.HSK.DLY = %p)", man.CFG.HSK.DLY, sub.CFG.HSK.DLY);

        assert (man.CFG.BUS == sub.CFG.BUS) else $error("Parameter (man.CFG.BUS = %p) != (sub.CFG.BUS = %p)", man.CFG.BUS, sub.CFG.BUS);
    end
`endif

////////////////////////////////////////////////////////////////////////////////
// register response path
////////////////////////////////////////////////////////////////////////////////

    // handshake
    assign man.vld = sub.vld;

    // request
    assign man.req.lck = sub.req.lck;
    assign man.req.ndn = sub.req.ndn;
    assign man.req.wen = sub.req.wen;
    assign man.req.ren = sub.req.ren;
    assign man.req.ctl = sub.req.ctl;
    assign man.req.adr = sub.req.adr;
    assign man.req.siz = sub.req.siz;
    assign man.req.byt = sub.req.byt;
    assign man.req.wdt = sub.req.wdt;

    // response (data)
    generate
    case (OPT)
        "POWER": begin
            case (sub.CFG.BUS.MOD)
                1'b0: begin: byt
                    // read data (logarithmic size)
                    for (genvar i=0; i<sub.CFG_BUS_BYT; i++) begin: rdt
                        always_ff @(posedge man.clk)
                        if (man.trn_dly[man.CFG.HSK.DLY] & sub.req.ren) begin
                            if (i < (1<<sub.req.siz)) begin
                                sub.rsp.rdt[i*8+:8] <= man.rsp.rdt[i*8+:8]; 
                            end
                        end
                    end: rdt
                end: byt
                1'b1: begin: byt
                    // read data (byte enable)
                    for (genvar i=0; i<sub.CFG_BUS_BYT; i++) begin: rdt
                        always_ff @(posedge man.clk)
                        if (man.trn_dly[man.CFG.HSK.DLY] & sub.req.ren) begin
                            if (sub.req.byt[i]) begin
                                sub.rsp.rdt[i*8+:8] <= man.rsp.rdt[i*8+:8];
                            end
                        end
                    end: rdt
                end: byt
            endcase
        end
        "COMPLEXITY": begin
            always_ff @(posedge sub.clk)
            if (man.trn_dly[man.CFG.HSK.DLY] & sub.req.ren) begin
                sub.rsp.rdt <= man.rsp.rdt;
            end
        end
    endcase
    endgenerate

    // response (error)
    always_ff @(posedge man.clk)
    begin
        if (man.trn_dly[man.CFG.HSK.DLY]) begin
            sub.rsp.sts <= man.rsp.sts;
            sub.rsp.err <= man.rsp.err;
        end
    end

    // handshake
    assign sub.rdy = man.rdy;

endmodule: tcb_lite_lib_register_response
