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
// transfer response queue and driver
////////////////////////////////////////////////////////////////////////////////

    // transfer response structure
    typedef sub.rsp_t rsp_t;

    // transfer response queue type
    typedef struct {
        rsp_t        rsp;  // TCB response structure
        int unsigned bpr;  // backpressure cycles number
    } rsp_que_t;

    // transfer response queue
    rsp_que_t rsp_que [$];

    // response without delay
    rsp_t sub_rsp;

    // transfer response initialization
    initial begin
        sub.rdy = 1'b0;
        sub_rsp = '{default: 'x};
    end

    // transfer response driver
    always @(rsp_que.size())
    begin: driver
        static int unsigned idl = 0;
        if (rsp_que.size() > 0) begin
            // backpressure cycles
            while (rsp_que[0].bpr > 0) begin
                @(posedge sub.clk);
                rsp_que[0].bpr--;
            end
            // drive response
            sub.rdy <= 1'b1;
            sub_rsp <= rsp_que[0].rsp;
            // idle cycles
            do begin
                @(posedge sub.clk);
                idl++;
            end while (~sub.trn);
            // remove response
            sub.rdy <= 1'b0;
            sub_rsp <= '{default: 'x};
            void'(rsp_que.pop_front());
        end else begin
            sub.rdy <= 1'b0;
            sub_rsp <= '{default: 'x};
        end
    end: driver

    // delayed response
    assign sub.rsp = $past(sub_rsp, sub.DLY, , @(posedge sub.clk));

////////////////////////////////////////////////////////////////////////////////
// transfer request queue and sampler
////////////////////////////////////////////////////////////////////////////////

    // transfer request structure
    typedef sub.req_t req_t;

    // transfer request queue type
    typedef struct {
        req_t        req;  // TCB request structure
        int unsigned idl;  // idle cycles number
    } req_que_t;

    // transfer request queue
    req_que_t req_que [$];

    // transfer request sampler
    always_ff @(posedge sub.clk)
    begin: sampler
        if (sub.trn) begin
            req_que.push_back('{req: sub.req, idl: driver.idl});
        end
    end: sampler

    // TODO: enable/disable transfer logger
    // this will allow for proper measuring of idle times

endmodule: tcb_lite_vip_subordinate
