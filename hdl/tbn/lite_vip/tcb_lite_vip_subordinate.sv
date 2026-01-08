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

module tcb_lite_vip_subordinate (
    // system bus interface
    tcb_lite_if.sub tcb
);

    // local parameters
    localparam int unsigned DLY = tcb.DLY;
    localparam int unsigned DAT = tcb.DAT;
    localparam int unsigned ADR = tcb.ADR;
    localparam int unsigned BYT = tcb.BYT;
    localparam int unsigned SIZ = tcb.SIZ;

////////////////////////////////////////////////////////////////////////////////
// TCB access
////////////////////////////////////////////////////////////////////////////////

    // response is immediate
    assign tcb.rdy = 1'b1;

    // read data is don't care
    assign tcb.rdt_dly[0] = 'x;

    // the response status is always an error
    assign tcb.err_dly[0] = 1'b1;

////////////////////////////////////////////////////////////////////////////////
// transfer response pipeline
////////////////////////////////////////////////////////////////////////////////

    // transfer response structure
    typedef struct {
        logic [DAT-1:0] rdt;
        logic           err;
    } rsp_t;

    rsp_t rsp [$];

    always_ff @(posedge tcb.clk)
    begin
        if (tcb.trn_dly[DLY]) begin
            rsp.push_back('{tcb.rdt, tcb.err});
        end
    end

endmodule: tcb_lite_vip_subordinate
