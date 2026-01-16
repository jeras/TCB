////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) VIP (Verification IP) protocol checker
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

module tcb_lite_vip_protocol_checker
    import tcb_lite_pkg::*;
(
    // TCB interface
    tcb_lite_if.mon tcb
);

////////////////////////////////////////////////////////////////////////////////
// handshake layer
////////////////////////////////////////////////////////////////////////////////

    always_ff @(posedge tcb.clk)
    if ($realtime > 0) begin
        // valid/ready known
        assert (!$isunknown(tcb.vld)) else $error("TCB: tcb.vld is unknown.");
        // reset state
        if (tcb.rst) begin
            assert(~tcb.vld) else $error("TCB: valid must be low during reset.");
        end
        // reset sequence
        if ($fell(tcb.rst)) begin
            assert(~tcb.vld) else $error("TCB: valid must be low during first cycle after reset release.");
        end
        // while valid
        if (tcb.vld == 1'b1) begin
            // ready known
            assert (!$isunknown(tcb.rdy)) else $error("TCB: tcb.rdy is unknown during a valid cycle.");
            // while stalling
            if ($past(tcb.stl)) begin
//                assert ($stable(tcb.req)) else $error("TCB: tcb.req is unstable during a stall.");
            end
        end
        // read data hold (HSK.DLY>1)
        // TODO
    end

////////////////////////////////////////////////////////////////////////////////
// bus layer
////////////////////////////////////////////////////////////////////////////////

    // request
    always_ff @(posedge tcb.clk)
    if ($realtime > 0) begin
        // while valid
        if (tcb.vld == 1'b1) begin
            // lock
            assert (!$isunknown(tcb.req.lck)) else $error("TCB: tcb.req.lck is unknown during a transfer cycle.");
            // endianness
            assert (!$isunknown(tcb.req.ndn)) else $error("TCB: tcb.req.ndn is unknown during a transfer cycle.");
            // write enable
            assert (!$isunknown(tcb.req.wen)) else $error("TCB: tcb.req.wen is unknown during a transfer cycle.");
            // address
            assert (!$isunknown(tcb.req.adr & tcb.MSK)) else $error("TCB: tcb.req.adr is unknown during a transfer cycle.");
            if (tcb.MOD == 1'b0) begin
                // transfer size
                assert (!$isunknown(tcb.req.siz)) else $error("TCB: tcb.req.siz is unknown during a transfer cycle.");
                assert (tcb.req.siz > tcb.SIZ'(2)) else $error("TCB: tcb.req.siz is outside range.");  // TODO: fix formula
                // write data
                if (tcb.req.wen == 1'b1) begin
                    for (int unsigned i=0; i<2**tcb.req.siz; i++) begin
                        assert (!$isunknown(tcb.req.wdt[8*i+:8])) else $error("TCB: tcb.req.wdt[8*%0d+:8] is unknown during a transfer cycle.", i);
                    end
                end
            end
            if (tcb.MOD == 1'b1) begin
                // byte enable
                assert (!$isunknown(tcb.req.byt)) else $error("TCB: tcb.req.byt is unknown during a transfer cycle.");
                // TODO: add checks for valid byte enable combinations
                // write data
                if (tcb.req.wen == 1'b1) begin
                    for (int unsigned i=0; i<tcb.BYT; i++) begin
                        if (tcb.req.byt[i]) begin 
                            assert (!$isunknown(tcb.req.wdt[8*i+:8])) else $error("TCB: tcb.req.wdt[8*%0d+:8] is unknown during a transfer cycle.", i);
                        end
                    end
                end
            end
        end
    end

    // response
    always_ff @(posedge tcb.clk)
    if ($realtime > 0) begin
        // response/read data bus and data sizing
        if (tcb.trn_dly[tcb.DLY]) begin
            if (~tcb.req_dly[tcb.DLY].wen) begin
                if (tcb.MOD == 1'b0) begin
                    for (int unsigned i=0; i<2**tcb.req_dly[tcb.DLY].siz; i++) begin
                        assert (!$isunknown(tcb.rsp.rdt[8*i+:8])) else $error("TCB: tcb.rsp.rdt[%0d] is unknown during a transfer cycle.", i);
                    end
                end
                if (tcb.MOD == 1'b1) begin
                    for (int unsigned i=0; i<tcb.BYT; i++) begin
                        if (tcb.req_dly[tcb.DLY].byt[i]) begin
                            assert (!$isunknown(tcb.rsp.rdt[8*i+:8])) else $error("TCB: tcb.rsp.rdt[%0d] is unknown during a transfer cycle.", i);
                        end
                    end
                end
            end
            // response status check
            assert (!$isunknown(tcb.rsp.err)) else $error("TCB: tcb.rsp.sts is unknown during a transfer cycle.");
        end
    end

////////////////////////////////////////////////////////////////////////////////
// BMA layer
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Transaction framing layer
////////////////////////////////////////////////////////////////////////////////

endmodule: tcb_lite_vip_protocol_checker
