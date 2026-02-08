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
    // TCB-Lite interfaces
    tcb_lite_if.sub sub,  // TCB subordinate interface (manager     device connects here)
    tcb_lite_if.man man   // TCB manager     interface (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    // BUS parameters
    initial
    begin
        assert (man.CFG.HSK.DLY == sub.CFG.HSK.DLY) else $error("Parameter (man.CFG.HSK.DLY = %p) != (sub.CFG.HSK.DLY = %p)", man.CFG.HSK.DLY, sub.CFG.HSK.DLY);
        assert (man.CFG.BUS.DAT == sub.CFG.BUS.DAT) else $error("Parameter (man.CFG.BUS.DAT = %p) != (sub.CFG.BUS.DAT = %p)", man.CFG.BUS.DAT, sub.CFG.BUS.DAT);
        assert (man.CFG.BUS.ADR == sub.CFG.BUS.ADR) else $error("Parameter (man.CFG.BUS.ADR = %p) != (sub.CFG.BUS.ADR = %p)", man.CFG.BUS.ADR, sub.CFG.BUS.ADR);
//        assert (man.MSK == sub.MSK) else $error("Parameter (man.MSK = %p) != (sub.MSK = %p)", man.MSK, sub.MSK);

        assert (man.CFG.BUS.MOD == 1'b1) else $error("Parameter (man.CFG.BUS.MOD = %p) != 1'b1", man.CFG.BUS.MOD);
        assert (sub.CFG.BUS.MOD == 1'b0) else $error("Parameter (sub.CFG.BUS.MOD = %p) != 1'b0", sub.CFG.BUS.MOD);
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
    assign man.req.ren = sub.req.ren;
    assign man.req.ctl = sub.req.ctl;
    assign man.req.adr = sub.req.adr;
    assign man.req.siz = sub.req.siz;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // request/response
    logic                       req_ndn, rsp_ndn;  // endianness
    logic [sub.CFG_BUS_OFF-1:0] req_off, rsp_off;  // address offset
    logic [sub.CFG_BUS_SIZ-1:0] req_siz, rsp_siz;  // logarithmic size

    // manager/subordinate read/write data
    logic [sub.CFG_BUS_BYT-1:0][8-1:0] sub_wdt, man_wdt;
    logic [sub.CFG_BUS_BYT-1:0][8-1:0] sub_rdt, man_rdt;

    // prefix OR operation
    function automatic [sub.CFG_BUS_OFF-1:0] prefix_or (
        input logic [sub.CFG_BUS_OFF-1:0] val
    );
        prefix_or[sub.CFG_BUS_OFF-1] = val[sub.CFG_BUS_OFF-1];
        for (int unsigned i=sub.CFG_BUS_OFF-1; i>0; i--) begin
            prefix_or[i-1] = prefix_or[i] | val[i-1];
        end
    endfunction: prefix_or

    // request/response endianness
    assign req_ndn = sub.req_dly[0              ].ndn;
    assign rsp_ndn = sub.req_dly[sub.CFG.HSK.DLY].ndn;

    // request/response logarithmic size
    assign req_siz = sub.req_dly[0              ].siz;
    assign rsp_siz = sub.req_dly[sub.CFG.HSK.DLY].siz;

    // request/response address offset
    assign req_off = sub.req_dly[0              ].adr[$clog2(sub.CFG_BUS_BYT)-1:0];
    assign rsp_off = sub.req_dly[sub.CFG.HSK.DLY].adr[$clog2(sub.CFG_BUS_BYT)-1:0];

////////////////////////////////////////////////////////////////////////////////
// multiplexers
////////////////////////////////////////////////////////////////////////////////

    // local data signals
    assign sub_wdt = sub.req.wdt;
    assign man_rdt = man.rsp.rdt;

    generate
    if (ALIGNED == 1'b1) begin: aligned

        // offset mask
        logic [sub.CFG_BUS_OFF-1:0] req_msk;

        // offset mask
        for (genvar i=0; i<sub.CFG_BUS_OFF; i++) begin
            assign req_msk[i] = (i >= req_siz);
        end

        // byte enable
        for (genvar i=0; i<sub.CFG_BUS_BYT; i++) begin
            assign man.req.byt[i] = (req_off & req_msk) == (i[sub.CFG_BUS_OFF-1:0] & req_msk);
        end

        // TODO: add big endian support, maybe ASCENDING also

        // write access
        for (genvar i=0; i<sub.CFG_BUS_BYT; i++) begin
            assign man_wdt[i] = sub_wdt[i[sub.CFG_BUS_OFF-1:0] & ~req_msk];
        end

        // read access
        for (genvar i=0; i<sub.CFG_BUS_BYT; i++) begin
            assign sub_rdt[i] = man_rdt[(~prefix_or(i[sub.CFG_BUS_OFF-1:0]) & rsp_off) | i[sub.CFG_BUS_OFF-1:0]];
        end

    end: aligned
    else begin: unaligned

        // byte enable
        logic [sub.CFG_BUS_BYT-1:0] sub_req_ben;

        // logarithmic size mode (subordinate interface) byte enable
        for (genvar i=0; i<sub.CFG_BUS_BYT; i++) begin: logsize2byteena
            assign sub_req_ben[i] = (i < (1<<req_siz)) ? 1'b1 : 1'b0;
        end: logsize2byteena

        // byte enable
        for (genvar i=0; i<sub.CFG_BUS_BYT; i++) begin: ben
            assign man.req.byt[i] = sub_req_ben[(i-integer'(req_off)) % sub.CFG_BUS_BYT];
        end: ben

        // write data
        for (genvar i=0; i<sub.CFG_BUS_BYT; i++) begin: wdt
            always_comb
            unique case (req_ndn)
                1'b0   :  man_wdt[i] = sub_wdt[(               i-integer'(req_off)) % sub.CFG_BUS_BYT];
                1'b1   :  man_wdt[i] = sub_wdt[((1<<req_siz)-1-i+integer'(req_off)) % sub.CFG_BUS_BYT];
                default:  man_wdt[i] = 8'hxx;
            endcase
        end: wdt

        // read data
        for (genvar i=0; i<sub.CFG_BUS_BYT; i++) begin: rdt
            always_comb
            unique case (rsp_ndn)
                1'b0   :  sub_rdt[i] = man_rdt[(               i+integer'(rsp_off)) % sub.CFG_BUS_BYT];
                1'b1   :  sub_rdt[i] = man_rdt[((1<<req_siz)-1-i+integer'(rsp_off)) % sub.CFG_BUS_BYT];
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
