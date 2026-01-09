////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library register slice for backpressure path
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

module tcb_lite_lib_register_backpressure (
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
        assert (man.DLY == sub.DLY) else $error("Parameter (man.DLY = %p) != (sub.DLY = %p)", man.DLY, sub.DLY);
        assert (man.DAT == sub.DAT) else $error("Parameter (man.DAT = %p) != (sub.DAT = %p)", man.DAT, sub.DAT);
        assert (man.ADR == sub.ADR) else $error("Parameter (man.ADR = %p) != (sub.ADR = %p)", man.ADR, sub.ADR);
        assert (man.MSK == sub.MSK) else $error("Parameter (man.MSK = %p) != (sub.MSK = %p)", man.MSK, sub.MSK);
        assert (man.MOD == sub.MOD) else $error("Parameter (man.MOD = %p) != (sub.MOD = %p)", man.MOD, sub.MOD);
    end
`endif

////////////////////////////////////////////////////////////////////////////////
// register backpressure path
////////////////////////////////////////////////////////////////////////////////

    typedef sub.req_t req_t;

    // request temporary buffer
    req_t tmp_req;

    // handshake
    assign man.vld = sub.rdy ? sub.vld : 1'b1;

    // request buffer
    always_ff @(posedge sub.clk)
    begin
        if (sub.vld & sub.rdy & ~man.rdy) begin
            tmp_req.lck <= sub.req.lck;
            tmp_req.ndn <= sub.req.ndn;
            tmp_req.wen <= sub.req.wen;
            tmp_req.adr <= sub.req.adr;
            if (sub.MOD == 1'b0)  tmp_req.siz <= sub.req.siz;  // logarithmic size
            else                  tmp_req.byt <= sub.req.byt;  // byte enable
            if (sub.req.wen) begin
                for (int unsigned i=0; i<sub.BYT; i++) begin
                    if (sub.MOD == 1'b0)  if (i < 2**sub.req.siz   ) tmp_req.wdt[i*8+:8] <= sub.req.wdt[i*8+:8];  // logarithmic size
                    else                  if (       sub.req.byt[i]) tmp_req.wdt[i*8+:8] <= sub.req.wdt[i*8+:8];  // byte enable
                end
            end
        end
    end

    // request
`ifdef SLANG
    assign man.req.lck = sub.rdy ? sub.req.lck : tmp_req.lck;
    assign man.req.ndn = sub.rdy ? sub.req.ndn : tmp_req.ndn;
    assign man.req.wen = sub.rdy ? sub.req.wen : tmp_req.wen;
    assign man.req.adr = sub.rdy ? sub.req.adr : tmp_req.adr;
    assign man.req.siz = sub.rdy ? sub.req.siz : tmp_req.siz;
    assign man.req.byt = sub.rdy ? sub.req.byt : tmp_req.byt;
    assign man.req.wdt = sub.rdy ? sub.req.wdt : tmp_req.wdt;
`else
    assign man.req = sub.rdy ? sub.req : tmp_req;
`endif

    // response
    assign sub.rsp.rdt = man.rsp.rdt;
    assign sub.rsp.err = man.rsp.err;

    // handshake
    always_ff @(posedge sub.clk, posedge sub.rst)
    if (sub.rst) begin
        sub.rdy <= 1'b1;
    end else begin
        if (sub.rdy)  sub.rdy <= ~(sub.vld & ~man.rdy);
        else          sub.rdy <=              man.rdy ;
    end

endmodule: tcb_lite_lib_register_backpressure
