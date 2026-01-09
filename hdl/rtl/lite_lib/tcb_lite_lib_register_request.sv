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

module tcb_lite_lib_register_request (
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
    begin
        man.req.wen <= sub.req.wen;
        man.req.lck <= sub.req.lck;
        man.req.adr <= sub.req.adr;
        if (sub.MOD == 1'b0)  man.req.siz <= sub.req.siz;  // logarithmic size
        else                  man.req.byt <= sub.req.byt;  // byte enable
        if (sub.req.wen) begin
            for (int unsigned i=0; i<sub.BYT; i++) begin
                if (sub.MOD == 1'b0)  if (i < 2**sub.req.siz) man.req.wdt[i*8+:8] <= sub.req.wdt[i*8+:8];  // logarithmic size
                else                  if (sub.req.byt[i])     man.req.wdt[i*8+:8] <= sub.req.wdt[i*8+:8];  // byte enable
            end
        end
    end

    // response
    assign sub.rsp.rdt = man.rsp.rdt;
    assign sub.rsp.err = man.rsp.err;

    // handshake (valid is checked to avoid pipeline bubbles)
    assign sub.rdy = man.rdy | ~man.vld;

endmodule: tcb_lite_lib_register_request
