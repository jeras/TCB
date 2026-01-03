////////////////////////////////////////////////////////////////////////////////
// TCB lite (Tightly Coupled Bus) library register slice for response path
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

module tcb_lite_lib_register_response (
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
// register response path
////////////////////////////////////////////////////////////////////////////////

    // handshake
    assign man.vld = sub.vld;

    // request
    assign man.wen = sub.wen;
    assign man.lck = sub.lck;
    assign man.adr = sub.adr;
    assign man.siz = sub.siz;
    assign man.byt = sub.byt;
    assign man.wdt = sub.wdt;

    // response
    always_ff @(posedge man.clk)
    begin
        // TODO: only on read enable, and byte enable (problem is what to do with LOG_SIZE
        if (man.dly[man.DELAY]) begin
            if (~sub.wen) begin
                for (int unsigned i=0; i<sub.WIDTH/8; i++) begin
                    if (sub.MODE == 1'b0)  if (i < 2**sub.siz) sub.rdt[i*8+:8] <= man.rdt[i*8+:8];  // logarithmic size
                    else                   if (sub.byt[i])     sub.rdt[i*8+:8] <= man.rdt[i*8+:8];  // byte enable
                end
            end
            sub.err <= man.err;
        end
    end

    // handshake
    assign sub.rdy = man.rdy;

endmodule: tcb_lite_lib_register_response
