////////////////////////////////////////////////////////////////////////////////
// TCB lite (Tightly Coupled Bus) library log. size to byte enable mode conversion
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

module tcb_lite_lib_siz2byt #(
    parameter bit ALIGNED = 1'b1
)(
    // interfaces
    tcb_lite_if.sub sub,    // TCB subordinate interface (manager     device connects here)
    tcb_lite_if.man man     // TCB manager     interface (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    // BUS parameters
    initial
    begin
        assert (man.DELAY == sub.DELAY) else $error("Parameter (man.DELAY = %p) != (sub.DELAY = %p)", man.DELAY, sub.DELAY);
        assert (man.WIDTH == sub.WIDTH) else $error("Parameter (man.WIDTH = %p) != (sub.WIDTH = %p)", man.WIDTH, sub.WIDTH);
        assert (man.MASK  == sub.MASK ) else $error("Parameter (man.MASK  = %p) != (sub.MASK  = %p)", man.MASK , sub.MASK );
        assert (man.MODE  == 1'b1)      else $error("Parameter (man.MODE  = %p) != 1'b1"            , man.MODE);
        assert (sub.MODE  == 1'b0)      else $error("Parameter (sub.MODE  = %p) != 1'b0"            , sub.MODE);
    end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

    // handshake
    assign man.vld = sub.vld;

    // request
    assign man.lck = sub.lck;
    assign man.wen = sub.wen;
    assign man.adr = sub.adr;
    assign man.siz = sub.siz;
    assign man.byt = sub.byt;
    assign man.wdt = sub.wdt;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // request/response address offset, logarithmic size
    logic [$clog2(sub.WIDTH)-1:0] req_off, rsp_off;
    logic [                2-1:0] req_siz, rsp_siz;

    // endianness
    logic                   req_ndn, rsp_ndn;

    // prefix OR operation
    function automatic [sub.WIDTH/8-1:0] prefix_or (
        input logic [sub.WIDTH/8-1:0] val
    );
        prefix_or[sub.WIDTH/8-1] = val[sub.WIDTH/8-1];
        for (int unsigned i=sub.WIDTH/8-1; i>0; i--) begin
            prefix_or[i-1] = prefix_or[i] | val[i-1];
        end
    endfunction: prefix_or

    // request/response address offset, logarithmic size
    assign req_off = sub.req                     .adr[sub.WIDTH/8-1:0];
    assign rsp_off = sub.req_dly[sub.CFG.HSK.DLY].adr[sub.WIDTH/8-1:0];
    assign req_siz = sub.req                     .siz;
    assign rsp_siz = sub.req_dly[sub.CFG.HSK.DLY].siz;

    // endianness
    assign req_ndn = sub.req                     .ndn;
    assign rsp_ndn = sub.req_dly[man.CFG.HSK.DLY].ndn;

////////////////////////////////////////////////////////////////////////////////
// multiplexers
////////////////////////////////////////////////////////////////////////////////

    generate
    if (ALIGNED == 1'b1) begin: aligned

        // offset mask
        logic [sub.WIDTH/8-1:0] req_msk;

        // offset mask
        always_comb
        for (int unsigned i=0; i<sub.WIDTH/8; i++) begin
            req_msk[i] = (i >= sub.siz);
        end

        // byte enable
        always_comb
        for (int unsigned i=0; i<sub.WIDTH/8; i++) begin
            man.byt[i] = (req_off & req_msk) == (i[sub.WIDTH/8-1:0] & req_msk);
        end

        // TODO: add big endian support, maybe ASCENDING also

        // write access
        always_comb
        for (int unsigned i=0; i<sub.WIDTH/8; i++) begin
            man.wdt[i] = sub.wdt[i[sub.WIDTH/8-1:0] & ~req_msk];
        end

        // read access
        always_comb
        for (int unsigned i=0; i<sub.WIDTH/8; i++) begin
            sub.rdt[i] = man.rdt[(~prefix_or(i[sub.WIDTH/8-1:0]) & rsp_off) | i[sub.WIDTH/8-1:0]];
        end

    end: aligned
    else begin: unaligned

        // byte enable
        logic [sub.WIDTH/8-1:0] sub_req_ben;

        // logarithmic size mode (subordinate interface) byte enable
        always_comb
        for (int unsigned i=0; i<sub.WIDTH/8; i++) begin: logsize2byteena
            sub_req_ben[i] = (i < 2**sub.siz) ? 1'b1 : 1'b0;
        end: logsize2byteena

        // byte enable
        always_comb
        for (int unsigned i=0; i<sub.WIDTH/8; i++) begin: ben
            man.byt[i] = sub_req_ben[(i-integer'(req_off)) % sub.WIDTH/8];
        end: ben

        // write data
        always_comb
        for (int unsigned i=0; i<sub.WIDTH/8; i++) begin: wdt
            unique case (req_ndn)
                TCB_LITTLE:  man.wdt[i] = sub.wdt[(             i-integer'(req_off)) % sub.WIDTH/8];
                TCB_BIG   :  man.wdt[i] = sub.wdt[(2**req_siz-1-i+integer'(req_off)) % sub.WIDTH/8];
                default   :  man.wdt[i] = 8'hxx;
            endcase
        end: wdt

        // read data
        always_comb
        for (int unsigned i=0; i<sub.WIDTH/8; i++) begin: rdt
            unique case (rsp_ndn)
                TCB_LITTLE:  sub.rdt[i] = man.rdt[(             i+integer'(rsp_off)) % sub.WIDTH/8];
                TCB_BIG   :  sub.rdt[i] = man.rdt[(2**rsp_siz-1-i+integer'(rsp_off)) % sub.WIDTH/8];
                default   :  sub.rdt[i] = 8'hxx;
            endcase
        end: rdt

    end: unaligned
    endgenerate

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

    // response status error
    assign sub.err = man.err;

    // handshake
    assign sub.rdy = man.rdy;

endmodule: tcb_lite_lib_siz2byt
