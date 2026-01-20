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
    typedef mon.req_t req_t;
    typedef mon.rsp_t rsp_t;

    // transfer request/response queue type
    typedef struct {
        req_t        req;  // TCB request structure
        rsp_t        rsp;  // TCB response structure
        int unsigned idl;  // idle cycles number
        int unsigned bpr;  // backpressure cycles number
    } bus_que_t;

    // transfer request queue
    bus_que_t bus_que [$];

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
            bus_que.push_back('{req: $past(mon.req, mon.DLY), rsp: mon.rsp, idl: $past(idl, mon.DLY), bpr: $past(bpr, mon.DLY)});
        end
    end: sampler

endmodule: tcb_lite_vip_monitor
