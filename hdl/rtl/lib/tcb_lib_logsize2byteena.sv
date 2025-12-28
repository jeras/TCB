////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library log. size to byte enable mode conversion
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

module tcb_lib_logsize2byteena
    import tcb_pkg::*;
(
    // interfaces
    tcb_if.sub sub,    // TCB subordinate interface (manager     device connects here)
    tcb_if.man man     // TCB manager     interface (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    // BUS parameters
    initial begin
        // data sizing mode
        assert (sub.CFG.BUS.MOD == TCB_MOD_LOG_SIZE) else $error("mismatch (sub.CFG.BUS.MOD = %0s) != TCB_MOD_LOG_SIZE", sub.CFG.BUS.MOD.name());
        assert (man.CFG.BUS.MOD == TCB_MOD_BYTE_ENA) else $error("mismatch (man.CFG.BUS.MOD = %0s) != TCB_MOD_BYTE_ENA", man.CFG.BUS.MOD.name());
        // other parameters
        assert (  sub.CFG.BUS.LCK  ==   man.CFG.BUS.LCK ) else $error("mismatch (  sub.CFG.BUS.LCK  = %0d) != (  man.CFG.BUS.LCK  = %0d)", sub.CFG.BUS.LCK       , man.CFG.BUS.LCK       );
        assert (  sub.CFG.BUS.LEN  ==   man.CFG.BUS.LEN ) else $error("mismatch (  sub.CFG.BUS.LEN  = %0d) != (  man.CFG.BUS.LEN  = %0d)", sub.CFG.BUS.LEN       , man.CFG.BUS.LEN       );
        assert (  sub.CFG.BUS.CHN  ==   man.CFG.BUS.CHN ) else $error("mismatch (  sub.CFG.BUS.CHN  = %0s) != (  man.CFG.BUS.CHN  = %0s)", sub.CFG.BUS.CHN.name(), man.CFG.BUS.CHN.name());
        assert (  sub.CFG.BUS.PRF  ==   man.CFG.BUS.PRF ) else $error("mismatch (  sub.CFG.BUS.PRF  = %0s) != (  man.CFG.BUS.PRF  = %0s)", sub.CFG.BUS.PRF.name(), man.CFG.BUS.PRF.name());
        assert ($bits(sub.req.adr) == $bits(man.req.adr)) else $error("mismatch ($bits(sub.req.adr) = %0d) != ($bits(man.req.adr) = %0d)", $bits(sub.req.adr)    , $bits(man.req.adr)    );
        assert (  sub.CFG.BUS.NXT  ==   man.CFG.BUS.NXT ) else $error("mismatch (  sub.CFG.BUS.NXT  = %0s) != (  man.CFG.BUS.NXT  = %0s)", sub.CFG.BUS.NXT.name(), man.CFG.BUS.NXT.name());
        assert (  sub.CFG.BUS.ORD  ==   man.CFG.BUS.ORD ) else $error("mismatch (  sub.CFG.BUS.ORD  = %0s) != (  man.CFG.BUS.ORD  = %0s)", sub.CFG.BUS.ORD.name(), man.CFG.BUS.ORD.name());
        assert (  sub.CFG.BUS.NDN  ==   man.CFG.BUS.NDN ) else $error("mismatch (  sub.CFG.BUS.NDN  = %0s) != (  man.CFG.BUS.NDN  = %0s)", sub.CFG.BUS.NDN.name(), man.CFG.BUS.NDN.name());
    end

    generate
        if (sub.CFG.BUS.CHN != TCB_CHN_READ_ONLY) begin
            initial assert ($bits(sub.req.wdt) == $bits(man.req.wdt)) else $error("mismatch ($bits(sub.req.wdt) = %0d) != ($bits(man.req.wdt) = %0d)", $bits(sub.req.wdt), $bits(man.req.wdt));
        end
        if (sub.CFG.BUS.CHN != TCB_CHN_WRITE_ONLY) begin
            initial assert ($bits(sub.rsp.rdt) == $bits(man.rsp.rdt)) else $error("mismatch ($bits(sub.rsp.rdt) = %0d) != ($bits(man.rsp.rdt) = %0d)", $bits(sub.rsp.rdt), $bits(man.rsp.rdt));
        end
    endgenerate

    // PMA parameters
    initial begin
        assert (sub.CFG.PMA == man.CFG.PMA) else $error("mismatch (sub.CFG.PMA = %0d) != (man.CFG.PMA = %0d)", sub.CFG.PMA, man.CFG.PMA);
    end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

    // handshake
    assign man.vld = sub.vld;

    // request
    assign man.req.lck = sub.req.lck;
    assign man.req.ben = sub.req.ben;
    assign man.req.len = sub.req.len;
    assign man.req.wen = sub.req.wen;
    assign man.req.ren = sub.req.ren;
    assign man.req.aen = sub.req.aen;
    assign man.req.amo = sub.req.amo;
    assign man.req.rpt = sub.req.rpt;
    assign man.req.inc = sub.req.inc;
    assign man.req.adr = sub.req.adr;
    assign man.req.nxt = sub.req.nxt;
    assign man.req.ndn = sub.req.ndn;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // request/response address offset, logarithmic size
    logic [sub.CFG_BUS_MAX-1:0] req_off, rsp_off;
    logic [sub.CFG_BUS_SIZ-1:0] req_siz, rsp_siz;

    // endianness
    logic                   req_ndn, rsp_ndn;

    // prefix OR operation
    function automatic [sub.CFG_BUS_MAX-1:0] prefix_or (
        input logic [sub.CFG_BUS_MAX-1:0] val
    );
        prefix_or[sub.CFG_BUS_MAX-1] = val[sub.CFG_BUS_MAX-1];
        for (int unsigned i=sub.CFG_BUS_MAX-1; i>0; i--) begin
            prefix_or[i-1] = prefix_or[i] | val[i-1];
        end
    endfunction: prefix_or

    // request/response address offset, logarithmic size
    assign req_off = sub.req_dly[0              ].adr[sub.CFG_BUS_MAX-1:0];
    assign rsp_off = sub.req_dly[sub.CFG.HSK.DLY].adr[sub.CFG_BUS_MAX-1:0];
    assign req_siz = sub.req_dly[0              ].siz;
    assign rsp_siz = sub.req_dly[sub.CFG.HSK.DLY].siz;

    // endianness
    assign req_ndn = sub.req.                     ndn;
    assign rsp_ndn = sub.req_dly[man.CFG.HSK.DLY].ndn;

////////////////////////////////////////////////////////////////////////////////
// multiplexers
////////////////////////////////////////////////////////////////////////////////

    generate
    if (sub.CFG.PMA.ALN == sub.CFG_BUS_MAX) begin: aligned

        // offset mask
        logic [sub.CFG_BUS_MAX-1:0] req_msk;

        // offset mask
        always_comb
        for (int unsigned i=0; i<sub.CFG_BUS_MAX; i++) begin
            req_msk[i] = (i >= sub.req.siz);
        end

        // byte enable
        always_comb
        for (int unsigned i=0; i<sub.CFG_BUS_BYT; i++) begin
            man.req.byt[i] = (req_off & req_msk) == (i[sub.CFG_BUS_MAX-1:0] & req_msk);
        end

        // TODO: add big endian support, maybe ASCENDING also

        if (sub.CFG.BUS.CHN != TCB_CHN_READ_ONLY) begin: write
            // write access
            always_comb
            for (int unsigned i=0; i<sub.CFG_BUS_BYT; i++) begin
                man.req.wdt[i] = sub.req.wdt[i[sub.CFG_BUS_MAX-1:0] & ~req_msk];
            end
        end: write

        if (sub.CFG.BUS.CHN != TCB_CHN_WRITE_ONLY) begin: read
            // read access
            always_comb
            for (int unsigned i=0; i<sub.CFG_BUS_BYT; i++) begin
                sub.rsp.rdt[i] = man.rsp.rdt[(~prefix_or(i[sub.CFG_BUS_MAX-1:0]) & rsp_off) | i[sub.CFG_BUS_MAX-1:0]];
            end
        end: read

    end: aligned
    else begin: unaligned

        // byte enable
        logic [sub.CFG_BUS_BYT-1:0] sub_req_ben;

        // logarithmic size mode (subordinate interface) byte enable
        always_comb
        for (int unsigned i=0; i<sub.CFG_BUS_BYT; i++) begin: logsize2byteena
            sub_req_ben[i] = (i < 2**sub.req.siz) ? 1'b1 : 1'b0;
        end: logsize2byteena

        // byte enable
        always_comb
        for (int unsigned i=0; i<sub.CFG_BUS_BYT; i++) begin: ben
            man.req.byt[i] = sub_req_ben[(i-integer'(req_off)) % sub.CFG_BUS_BYT];
        end: ben

        if (sub.CFG.BUS.CHN != TCB_CHN_READ_ONLY) begin: write
            // write data
            always_comb
            for (int unsigned i=0; i<sub.CFG_BUS_BYT; i++) begin: wdt
                unique case (req_ndn)
                    TCB_LITTLE:  man.req.wdt[i] = sub.req.wdt[(             i-integer'(req_off)) % sub.CFG_BUS_BYT];
                    TCB_BIG   :  man.req.wdt[i] = sub.req.wdt[(2**req_siz-1-i+integer'(req_off)) % sub.CFG_BUS_BYT];
                    default   :  man.req.wdt[i] = 8'hxx;
                endcase
            end: wdt
        end: write

        if (sub.CFG.BUS.CHN != TCB_CHN_WRITE_ONLY) begin: read
            // read data
            always_comb
            for (int unsigned i=0; i<sub.CFG_BUS_BYT; i++) begin: rdt
                unique case (rsp_ndn)
                    TCB_LITTLE:  sub.rsp.rdt[i] = man.rsp.rdt[(             i+integer'(rsp_off)) % sub.CFG_BUS_BYT];
                    TCB_BIG   :  sub.rsp.rdt[i] = man.rsp.rdt[(2**rsp_siz-1-i+integer'(rsp_off)) % sub.CFG_BUS_BYT];
                    default   :  sub.rsp.rdt[i] = 8'hxx;
                endcase
            end: rdt
        end: read

    end: unaligned
    endgenerate

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

    // status error
    assign sub.rsp.sts = man.rsp.sts;

    // handshake
    assign sub.rdy = man.rdy;

endmodule: tcb_lib_logsize2byteena
