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
// TCB access
////////////////////////////////////////////////////////////////////////////////

    // response is immediate
    assign sub.rdy = 1'b1;

    // read data is don't care
    assign sub.rsp_dly[0].rdt = 'x;

    // the response status is always an error
    assign sub.rsp_dly[0].err =   'x;
    assign sub.rsp_dly[0].err = 1'b1;

////////////////////////////////////////////////////////////////////////////////
// transfer response pipeline
////////////////////////////////////////////////////////////////////////////////

    // transfer response structure
    typedef sub.rsp_t rsp_t;

    rsp_t rsp [$];

    always_ff @(posedge sub.clk)
    begin
        if (sub.trn_dly[sub.DLY]) begin
            rsp.push_back(sub.rsp);
        end
    end

endmodule: tcb_lite_vip_subordinate
