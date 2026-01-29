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
    tcb_lite_if.mon mon
);

////////////////////////////////////////////////////////////////////////////////
// handshake layer
////////////////////////////////////////////////////////////////////////////////

    always_ff @(posedge mon.clk)
    if ($realtime > 0) begin
        // valid/ready known
        assert (!$isunknown(mon.vld)) else $error("TCB: mon.vld is unknown.");
        // reset state
        if (mon.rst) begin
            assert(~mon.vld) else $error("TCB: valid must be low during reset.");
        end
        // reset sequence
        if ($fell(mon.rst)) begin
            assert(~mon.vld) else $error("TCB: valid must be low during first cycle after reset release.");
        end
        // while valid
        if (mon.vld == 1'b1) begin
            // ready known
            assert (!$isunknown(mon.rdy)) else $error("TCB: mon.rdy is unknown during a valid cycle.");
            // while stalling
            if ($past(mon.stl)) begin
//                assert ($stable(mon.req)) else $error("TCB: mon.req is unstable during a stall.");
            end
        end
        // read data hold (HSK.DLY>1)
        // TODO
    end

////////////////////////////////////////////////////////////////////////////////
// bus layer
////////////////////////////////////////////////////////////////////////////////

    // request
    always_ff @(posedge mon.clk)
    if ($realtime > 0) begin
        // while valid
        if (mon.vld == 1'b1) begin
            // lock
            assert (!$isunknown(mon.req.lck)) else $error("TCB: mon.req.lck is unknown during a transfer cycle.");
            // endianness
            assert (!$isunknown(mon.req.ndn)) else $error("TCB: mon.req.ndn is unknown during a transfer cycle.");
            // write enable
            assert (!$isunknown(mon.req.wen)) else $error("TCB: mon.req.wen is unknown during a transfer cycle.");
            // address
            // TODO: decide how to handle partial address decoders
//            assert (!$isunknown(mon.req.adr & mon.MSK)) else $error("TCB: mon.req.adr is unknown during a transfer cycle.");
            if (mon.MOD == 1'b0) begin
                // transfer size
                assert (!$isunknown(mon.req.siz)) else $error("TCB: mon.req.siz is unknown during a transfer cycle.");
                assert (mon.req.siz <= mon.SIZ'(mon.MAX)) else $error("TCB: mon.req.siz is outside range.");
                // write data
                if (mon.req.wen == 1'b1) begin
                    for (int unsigned i=0; i<2**mon.req.siz; i++) begin
                        assert (!$isunknown(mon.req.wdt[8*i+:8])) else $error("TCB: mon.req.wdt[8*%0d+:8] is unknown during a transfer cycle.", i);
                    end
                end
            end
            if (mon.MOD == 1'b1) begin
                // byte enable
                assert (!$isunknown(mon.req.byt)) else $error("TCB: mon.req.byt is unknown during a transfer cycle.");
                // TODO: add checks for valid byte enable combinations
                // write data
                if (mon.req.wen == 1'b1) begin
                    for (int unsigned i=0; i<mon.BYT; i++) begin
                        if (mon.req.byt[i]) begin 
                            assert (!$isunknown(mon.req.wdt[8*i+:8])) else $error("TCB: mon.req.wdt[8*%0d+:8] is unknown during a transfer cycle.", i);
                        end
                    end
                end
            end
        end
    end

    // response
    always_ff @(posedge mon.clk)
    if ($realtime > 0) begin
        // response/read data bus and data sizing
        if (mon.trn_dly[mon.DLY]) begin
            if (mon.req_dly[mon.DLY].ren) begin
                if (mon.MOD == 1'b0) begin
                    for (int unsigned i=0; i<2**mon.req_dly[mon.DLY].siz; i++) begin
                        assert (!$isunknown(mon.rsp.rdt[8*i+:8])) else $error("TCB: mon.rsp.rdt[%0d] is unknown during a transfer cycle.", i);
                    end
                end
                if (mon.MOD == 1'b1) begin
                    for (int unsigned i=0; i<mon.BYT; i++) begin
                        if (mon.req_dly[mon.DLY].byt[i]) begin
                            assert (!$isunknown(mon.rsp.rdt[8*i+:8])) else $error("TCB: mon.rsp.rdt[%0d] is unknown during a transfer cycle.", i);
                        end
                    end
                end
            end
            // response status check
            assert (!$isunknown(mon.rsp.err)) else $error("TCB: mon.rsp.sts is unknown during a transfer cycle.");
        end
    end

////////////////////////////////////////////////////////////////////////////////
// BMA layer
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Transaction framing layer
////////////////////////////////////////////////////////////////////////////////

endmodule: tcb_lite_vip_protocol_checker
