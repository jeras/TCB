////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) VIP monitor
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

module tcb_lite_vip_monitor
    import tcb_lite_pkg::*;
(
    // system bus interface
    tcb_lite_if.mon mon
);

////////////////////////////////////////////////////////////////////////////////
// transfer request/response queue and sampler
////////////////////////////////////////////////////////////////////////////////

    // transfer request/response structures
    typedef mon.vip_bus_t vip_bus_t;

    // transfer request queue
    vip_bus_t vip_bus [$];

    // idle/backpressure counters
    int unsigned idl = 0;
    int unsigned bpr = 0;

    // transfer request driver
    always @(posedge mon.clk)
    begin: monitor
        if (mon.trn) begin
            idl <= 0;
            bpr <= 0;
        end else begin
            if (~mon.vld &  mon.rdy)  idl <= idl+1;
            if ( mon.vld & ~mon.rdy)  bpr <= bpr+1;
        end
    end: monitor

    // transfer response sampler
    always_ff @(posedge mon.clk)
    begin: sampler
        if (mon.trn_dly[mon.DLY]) begin
            vip_bus.push_back('{
                req: '{req: $past(mon.req, mon.DLY), idl: $past(idl, mon.DLY)},
                rsp: '{rsp:       mon.rsp,           bpr: $past(bpr, mon.DLY)}
            });
        end
    end: sampler

endmodule: tcb_lite_vip_monitor
