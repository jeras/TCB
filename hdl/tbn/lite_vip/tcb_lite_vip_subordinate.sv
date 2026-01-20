////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) VIP subordinate model
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

module tcb_lite_vip_subordinate
    import tcb_lite_pkg::*;
(
    // system bus interface
    tcb_lite_if sub
);

////////////////////////////////////////////////////////////////////////////////
// transfer request queue and sampler
////////////////////////////////////////////////////////////////////////////////

    // transfer request structure
    typedef sub.vip_req_t vip_req_t;

    // transfer request queue
    vip_req_t vip_req [$];

    // transfer request sampler
    always_ff @(posedge sub.clk)
    begin: sampler
        if (sub.trn) begin
            vip_req.push_back('{req: sub.req, idl: driver.idl});
        end
    end: sampler

////////////////////////////////////////////////////////////////////////////////
// transfer response queue and driver
////////////////////////////////////////////////////////////////////////////////

    // transfer response structure
    typedef sub.vip_rsp_t vip_rsp_t;

    // transfer response queue
    vip_rsp_t vip_rsp [$];

    // transfer response initialization
    initial begin
        sub.rdy = 1'b0;
        sub.rsp_dly[0] = '{default: 'x};
    end

    // transfer response driver
    always @(vip_rsp.size())
    begin: driver
        static int unsigned idl = 0;
        if (vip_rsp.size() > 0) begin
            // backpressure cycles
            while (vip_rsp[0].bpr > 0) begin
                @(posedge sub.clk);
                vip_rsp[0].bpr--;
            end
            // drive response
            sub.rdy <= 1'b1;
//            sub.rsp_dly[0] <= vip_rsp[0].rsp;
            sub.rsp_dly[0].rdt <= vip_rsp[0].rsp.rdt;
            sub.rsp_dly[0].sts <= vip_rsp[0].rsp.sts;
            sub.rsp_dly[0].err <= vip_rsp[0].rsp.err;
            // idle cycles
            do begin
                @(posedge sub.clk);
                idl++;
            end while (~sub.trn);
            // remove response
            sub.rdy <= 1'b0;
            sub.rsp_dly[0] <= '{default: 'x};
            void'(vip_rsp.pop_front());
        end else begin
            sub.rdy <= 1'b0;
            sub.rsp_dly[0] <= '{default: 'x};
        end
    end: driver
    
endmodule: tcb_lite_vip_subordinate
