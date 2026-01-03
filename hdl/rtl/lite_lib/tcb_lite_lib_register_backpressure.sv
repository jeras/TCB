////////////////////////////////////////////////////////////////////////////////
// TCB lite (Tightly Coupled Bus) library register slice for backpressure path
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
        assert (man.DELAY == sub.DELAY) else $error("Parameter (man.DELAY = %p) != (sub.DELAY = %p)", man.DELAY, sub.DELAY);
        assert (man.WIDTH == sub.WIDTH) else $error("Parameter (man.WIDTH = %p) != (sub.WIDTH = %p)", man.WIDTH, sub.WIDTH);
        assert (man.MASK  == sub.MASK ) else $error("Parameter (man.MASK  = %p) != (sub.MASK  = %p)", man.MASK , sub.MASK );
        assert (man.MODE  == sub.MODE ) else $error("Parameter (man.MODE  = %p) != (sub.MODE  = %p)", man.MODE , sub.MODE );
    end
`endif

////////////////////////////////////////////////////////////////////////////////
// register backpressure path
////////////////////////////////////////////////////////////////////////////////

    // request temporary buffer
    logic                   lck;  // arbitration lock
    logic                   wen;  // write enable (0-read, 1-write)
    logic [sub.WIDTH  -1:0] adr;  // address
    logic [          2-1:0] siz;  // transfer size
    logic [sub.WIDTH/8-1:0] byt;  // byte enable
    logic [sub.WIDTH  -1:0] wdt;  // write data

    // handshake
    assign man.vld = sub.rdy ? sub.vld : 1'b1;

    // request buffer
    always_ff @(posedge sub.clk)
    begin
        if (sub.vld & sub.rdy & ~man.rdy) begin
            man.wen <= sub.wen;
            man.lck <= sub.lck;
            man.adr <= sub.adr;
            if (sub.MODE == 1'b0)  man.siz <= sub.siz;  // logarithmic size
            else                   man.byt <= sub.byt;  // byte enable
            if (sub.wen) begin
                for (int unsigned i=0; i<sub.WIDTH/8; i++) begin
                    if (sub.MODE == 1'b0)  if (i < 2**sub.siz) man.wdt[i*8+:8] <= sub.wdt[i*8+:8];  // logarithmic size
                    else                   if (sub.byt[i])     man.wdt[i*8+:8] <= sub.wdt[i*8+:8];  // byte enable
                end
            end
        end
    end

    // request
    assign man.lck = sub.rdy ? sub.lck : lck;
    assign man.wen = sub.rdy ? sub.wen : wen;
    assign man.adr = sub.rdy ? sub.adr : adr;
    assign man.siz = sub.rdy ? sub.siz : siz;
    assign man.byt = sub.rdy ? sub.byt : byt;
    assign man.wdt = sub.rdy ? sub.wdt : wdt;

    // response
    assign sub.rdt = man.rdt;
    assign sub.err = man.err;

    // handshake
    always_ff @(posedge sub.clk, posedge sub.rst)
    if (sub.rst) begin
        sub.rdy <= 1'b1;
    end else begin
        if (sub.rdy)  sub.rdy <= ~(sub.vld & ~man.rdy);
        else          sub.rdy <=              man.rdy ;
    end

endmodule: tcb_lite_lib_register_backpressure
