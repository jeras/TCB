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

module tcb_lite_lib_logsize2byteena
    import tcb_lite_pkg::*;
#(
    parameter bit ALIGNED = 1'b1
)(
    // interfaces
    tcb_lite_if.sub sub,  // TCB subordinate interface (manager     device connects here)
    tcb_lite_if.man man   // TCB manager     interface (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    // BUS parameters
    initial
    begin
        assert (man.DLY == sub.DLY) else $error("Parameter (man.DLY = %p) != (sub.DLY = %p)", man.DLY, sub.DLY);
        assert (man.DAT == sub.DAT) else $error("Parameter (man.DAT = %p) != (sub.DAT = %p)", man.DAT, sub.DAT);
        assert (man.ADR == sub.ADR) else $error("Parameter (man.ADR = %p) != (sub.ADR = %p)", man.ADR, sub.ADR);
//        assert (man.MSK == sub.MSK) else $error("Parameter (man.MSK = %p) != (sub.MSK = %p)", man.MSK, sub.MSK);

        assert (man.MOD == 1'b1)    else $error("Parameter (man.MOD = %p) != 1'b1"          , man.MOD);
        assert (sub.MOD == 1'b0)    else $error("Parameter (sub.MOD = %p) != 1'b0"          , sub.MOD);
    end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

    // handshake
    assign man.vld = sub.vld;

    // request
    assign man.req.lck = sub.req.lck;
    assign man.req.ndn = sub.req.ndn;
    assign man.req.wen = sub.req.wen;
    assign man.req.ctl = sub.req.ctl;
    assign man.req.adr = sub.req.adr;
    assign man.req.siz = sub.req.siz;
    assign man.req.byt = sub.req.byt;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // request/response
    logic               req_ndn, rsp_ndn;  // endianness
    logic [sub.MAX-1:0] req_off, rsp_off;  // address offset
    logic [sub.SIZ-1:0] req_siz, rsp_siz;  // logarithmic size

    // manager/subordinate read/write data
    logic [sub.BYT-1:0][8-1:0] sub_wdt, man_wdt;
    logic [sub.BYT-1:0][8-1:0] sub_rdt, man_rdt;

    // prefix OR operation
    function automatic [sub.MAX-1:0] prefix_or (
        input logic [sub.MAX-1:0] val
    );
        prefix_or[sub.MAX-1] = val[sub.MAX-1];
        for (int unsigned i=sub.MAX-1; i>0; i--) begin
            prefix_or[i-1] = prefix_or[i] | val[i-1];
        end
    endfunction: prefix_or

    // request/response endianness
    assign req_ndn = sub.req_dly[0      ].ndn;
    assign rsp_ndn = sub.req_dly[sub.DLY].ndn;

    // request/response address offset
    assign req_off = sub.req_dly[0      ].adr[$clog2(sub.BYT)-1:0];
    assign rsp_off = sub.req_dly[sub.DLY].adr[$clog2(sub.BYT)-1:0];

    // request/response logarithmic size
    assign req_siz = sub.req_dly[0      ].siz;
    assign rsp_siz = sub.req_dly[sub.DLY].siz;

////////////////////////////////////////////////////////////////////////////////
// multiplexers
////////////////////////////////////////////////////////////////////////////////

    // local data signals
    assign sub_wdt = sub.req.wdt;
    assign man_rdt = man.rsp.rdt;

    generate
    if (ALIGNED == 1'b1) begin: aligned

        // offset mask
        logic [sub.MAX-1:0] req_msk;

        // offset mask
        always_comb
        for (int unsigned i=0; i<sub.MAX; i++) begin
            req_msk[i] = (i >= req_siz);
        end

        // byte enable
        always_comb
        for (int unsigned i=0; i<sub.BYT; i++) begin
            man.req.byt[i] = (req_off & req_msk) == (i[sub.MAX-1:0] & req_msk);
        end

        // TODO: add big endian support, maybe ASCENDING also

        // write access
        always_comb
        for (int unsigned i=0; i<sub.BYT; i++) begin
            man_wdt[i] = sub_wdt[i[sub.MAX-1:0] & ~req_msk];
        end

        // read access
        always_comb
        for (int unsigned i=0; i<sub.BYT; i++) begin
            sub_rdt[i] = man_rdt[(~prefix_or(i[sub.MAX-1:0]) & rsp_off) | i[sub.MAX-1:0]];
        end

    end: aligned
    else begin: unaligned

        // byte enable
        logic [sub.BYT-1:0] sub_req_ben;

        // logarithmic size mode (subordinate interface) byte enable
        always_comb
        for (int unsigned i=0; i<sub.BYT; i++) begin: logsize2byteena
            sub_req_ben[i] = (i < 2**rsp_siz) ? 1'b1 : 1'b0;
        end: logsize2byteena

        // byte enable
        always_comb
        for (int unsigned i=0; i<sub.BYT; i++) begin: ben
            man.req.byt[i] = sub_req_ben[(i-integer'(req_off)) % sub.BYT];
        end: ben

        // write data
        always_comb
        for (int unsigned i=0; i<sub.BYT; i++) begin: wdt
            unique case (req_ndn)
                1'b0   :  man_wdt[i] = sub_wdt[(             i-integer'(req_off)) % sub.BYT];
                1'b1   :  man_wdt[i] = sub_wdt[(2**req_siz-1-i+integer'(req_off)) % sub.BYT];
                default:  man_wdt[i] = 8'hxx;
            endcase
        end: wdt

        // read data
        always_comb
        for (int unsigned i=0; i<sub.BYT; i++) begin: rdt
            unique case (rsp_ndn)
                1'b0   :  sub_rdt[i] = man_rdt[(             i+integer'(rsp_off)) % sub.BYT];
                1'b1   :  sub_rdt[i] = man_rdt[(2**rsp_siz-1-i+integer'(rsp_off)) % sub.BYT];
                default:  sub_rdt[i] = 8'hxx;
            endcase
        end: rdt

    end: unaligned
    endgenerate

    // local data signals
    assign sub.rsp.rdt = sub_rdt;
    assign man.req.wdt = man_wdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

    // response status/error
    assign sub.rsp.sts = man.rsp.sts;
    assign sub.rsp.err = man.rsp.err;

    // handshake
    assign sub.rdy = man.rdy;

endmodule: tcb_lite_lib_logsize2byteena
