////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library error subordinate
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

module tcb_lite_lib_error
    import tcb_lite_pkg::*;
(
    // system bus interface
    tcb_lite_if.sub sub,
    // default response status
    input  logic [sub.STS-1:0] sts
);

////////////////////////////////////////////////////////////////////////////////
// TCB access
////////////////////////////////////////////////////////////////////////////////

    // response is immediate
    assign sub.rdy = 1'b1;

    // read data is don't care
    assign sub.rsp.rdt = 'x;

    // the response status is always an error
    assign sub.rsp.sts =  sts;
    assign sub.rsp.err = 1'b1;

endmodule: tcb_lite_lib_error
