////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) VIP manager model
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

module tcb_lite_vip_manager
    import tcb_lite_pkg::*;
(
    // system bus interface
    tcb_lite_if.man man
);

////////////////////////////////////////////////////////////////////////////////
// transfer request driver
////////////////////////////////////////////////////////////////////////////////

    // request initialization into idle state
    initial begin
        // idle
        man.vld = 1'b0;
        // request don't care
        man.req = '{default: 'x};
    end
    
    // request driver
    task automatic req (
        // request
        input  logic               lck = 1'b0,
        input  logic               ndn = 1'b0,
        input  logic               wen,
        input  logic [man.CTL-1:0] ctl,
        input  logic [man.ADR-1:0] adr,
        input  logic [man.SIZ-1:0] siz = man.SIZ'($clog2(man.BYT)),
        input  logic [man.BYT-1:0] byt = '1,
        input  logic [man.DAT-1:0] wdt,
        // idle/backpressure timing
        input  int unsigned        idl = 0,
        output int unsigned        bpr
    );
        // cycle counter
        int unsigned cyc = 0;
        // sequence
        bpr = 0;
        do begin
            if (cyc == idl) begin
                // start handshake
                man.vld <= 1'b1;
                // request
                man.req.lck <= lck;
                man.req.ndn <= ndn;
                man.req.wen <= wen;
                man.req.ctl <= ctl;
                man.req.adr <= adr;
                man.req.siz <= siz;
                man.req.byt <= byt;
                man.req.wdt <= wdt;
            end
            @(posedge man.clk);
            if (~man.vld) cyc++;
            if (~man.rdy) bpr++;
        end while (~man.trn);
        // end handshake
        man.vld <= 1'b0;
        // request
        man.req.lck <= 'x;
        man.req.ndn <= 'x;
        man.req.wen <= 'x;
        man.req.ctl <= 'x;
        man.req.adr <= 'x;
        man.req.siz <= 'x;
        man.req.byt <= 'x;
        man.req.wdt <= 'x;
    endtask: req

////////////////////////////////////////////////////////////////////////////////
// transfer response queue
////////////////////////////////////////////////////////////////////////////////

    // transfer response structure
    typedef man.rsp_t rsp_t;

    rsp_t rsp [$];

    always_ff @(posedge man.clk)
    begin
        if (man.trn_dly[man.DLY]) begin
            rsp.push_back(man.rsp);
        end
    end

////////////////////////////////////////////////////////////////////////////////
// blocking write API
////////////////////////////////////////////////////////////////////////////////

    // manager endianness state
    bit cfg_ndn;

    // response signals sampled
    event               evn_rsp;
    logic [man.DAT-1:0] tmp_rdt;
    logic [man.STS-1:0] tmp_sts;
    logic               tmp_err;

    // manager endianness state
    initial cfg_ndn = 1'b0;

    task automatic access (
        input  logic               wen,
        input  logic [man.CTL-1:0] ctl,
        input  logic [man.ADR-1:0] adr,
        input  logic [man.DAT-1:0] wdt,
        output logic [man.DAT-1:0] rdt,
        output logic [man.STS-1:0] sts,
        output logic               err,
        input  int unsigned        len = man.DAT,
        input  logic               ndn = cfg_ndn
    );
        // local signals
        logic [man.SIZ-1:0] siz = 'x;
        logic [man.BYT-1:0] byt = 'x;
        logic [man.DAT-1:0] dat = 'x;
        // logarithmic size
        if (man.MOD == 1'b0) begin
            siz = man.SIZ'($clog2(len/8));
            for (int unsigned i=0; i<len/8; i++) begin
                if (wen) begin
                    dat[8*i+:8] = wdt[8*i+:8];
                end
            end
        end
        // byte enable
        if (man.MOD == 1'b1) begin
            byt = '1;
            for (int unsigned i=0; i<len/8; i++) begin
                int unsigned b = i+int'(adr[$clog2(man.BYT)-1:0]);
                byt[b] = 1'b1;
                if (wen) begin
                    dat[8*b+:8] = wdt[8*i+:8];
                end
            end
        end
        // transfer and delay
        fork
            begin: request
                int unsigned bpr;
                //   lck, ndn, wen, ctl, adr, siz, byt, wdt, idl, bpr
                req(1'b0, ndn, wen, ctl, adr, siz, byt, dat,   0, bpr);
            end: request
            begin: response
                do begin
                    @(posedge man.clk);
                end while (~man.trn_dly[man.DLY]);
                -> evn_rsp;
                tmp_rdt <= man.rsp.rdt;
                tmp_sts <= man.rsp.sts;
                tmp_err <= man.rsp.err;
                #1;  // TODO: without the unit delay, tmp_* signals do not propagate to the task output
            end: response
        join
        // logarithmic size
        if (man.MOD == 1'b0) begin
            for (int unsigned i=0; i<len/8; i++) begin
                if (~wen) begin
                    rdt[8*i+:8] = tmp_rdt[8*i+:8];
                end
            end
        end
        // byte enable
        if (man.MOD == 1'b1) begin
            byt = '1;
            for (int unsigned i=0; i<len/8; i++) begin
                int unsigned b = i+int'(adr[$clog2(man.BYT)-1:0]);
                if (~wen) begin
                    rdt[8*i+:8] = tmp_rdt[8*b+:8];
                end
            end
        end
        // response status/error
        sts = tmp_sts;
        err = tmp_err;
    endtask: access

////////////////////////////////////////////////////////////////////////////////
// blocking write API
////////////////////////////////////////////////////////////////////////////////

    task automatic write8 (
        input  logic [man.ADR-1:0] adr,
        input  logic [      8-1:0] dat,
        output logic [man.STS-1:0] sts,
        output logic               err,
        input  logic               ndn = 1'b0
    );
        logic [man.DAT-1:0] wdt = man.DAT'(dat);
        logic [man.DAT-1:0] rdt;
        //      wen, ctl, adr, wdt, rdt, sts, err, len, ndn
        access(1'b1,  'x, adr, wdt, rdt, sts, err,   8, ndn);
    endtask: write8

    task automatic write16 (
        input  logic [man.ADR-1:0] adr,
        input  logic [     16-1:0] dat,
        output logic [man.STS-1:0] sts,
        output logic               err,
        input  logic               ndn = 1'b0
    );
        logic [man.DAT-1:0] wdt = man.DAT'(dat);
        logic [man.DAT-1:0] rdt;
        //      wen, ctl, adr, wdt, rdt, sts, err, len, ndn
        access(1'b1,  'x, adr, wdt, rdt, sts, err,  16, ndn);
    endtask: write16

    task automatic write32 (
        input  logic [man.ADR-1:0] adr,
        input  logic [     32-1:0] dat,
        output logic [man.STS-1:0] sts,
        output logic               err,
        input  logic               ndn = 1'b0
    );
        logic [man.DAT-1:0] wdt = man.DAT'(dat);
        logic [man.DAT-1:0] rdt;
        //      wen, ctl, adr, wdt, rdt, sts, err, len, ndn
        access(1'b1,  'x, adr, wdt, rdt, sts, err,  32, ndn);
    endtask: write32

    task automatic write64 (
        input  logic [man.ADR-1:0] adr,
        input  logic [     64-1:0] dat,
        output logic [man.STS-1:0] sts,
        output logic               err,
        input  logic               ndn = 1'b0
    );
        logic [man.DAT-1:0] wdt = man.DAT'(dat);
        logic [man.DAT-1:0] rdt;
        //      wen, ctl, adr, wdt, rdt, sts, err, len, ndn
        access(1'b1,  'x, adr, wdt, rdt, sts, err,  64, ndn);
    endtask: write64

////////////////////////////////////////////////////////////////////////////////
// blocking read API
////////////////////////////////////////////////////////////////////////////////

    task automatic read8 (
        input  logic [man.ADR-1:0] adr,
        output logic [      8-1:0] dat,
        output logic [man.STS-1:0] sts,
        output logic               err,
        input  logic               ndn = 1'b0
    );
        logic [man.DAT-1:0] wdt = 'x;
        logic [man.DAT-1:0] rdt;
        //      wen, ctl, adr,          wdt , rdt, sts, err, len, ndn
        access(1'b0,  'x, adr, man.DAT'(wdt), rdt, sts, err,   8, ndn);
        dat = 8'(rdt);
    endtask: read8

    task automatic read16 (
        input  logic [man.ADR-1:0] adr,
        output logic [     16-1:0] dat,
        output logic [man.STS-1:0] sts,
        output logic               err,
        input  logic               ndn = 1'b0
    );
        logic [man.DAT-1:0] wdt = 'x;
        logic [man.DAT-1:0] rdt;
        //      wen, ctl, adr,          wdt , rdt, sts, err, len, ndn
        access(1'b0,  'x, adr, man.DAT'(wdt), rdt, sts, err,  16, ndn);
        dat = 16'(rdt);
    endtask: read16

    task automatic read32 (
        input  logic [man.ADR-1:0] adr,
        output logic [     32-1:0] dat,
        output logic [man.STS-1:0] sts,
        output logic               err,
        input  logic               ndn = 1'b0
    );
        logic [man.DAT-1:0] wdt = 'x;
        logic [man.DAT-1:0] rdt;
        //      wen, ctl, adr,          wdt , rdt, sts, err, len, ndn
        access(1'b0,  'x, adr, man.DAT'(wdt), rdt, sts, err,  32, ndn);
        dat = 32'(rdt);
    endtask: read32

    task automatic read64 (
        input  logic [man.DAT-1:0] adr,
        output logic [     64-1:0] dat,
        output logic [man.STS-1:0] sts,
        output logic               err,
        input  logic               ndn = 1'b0
    );
        logic [man.DAT-1:0] wdt = 'x;
        logic [man.DAT-1:0] rdt;
        //      wen, ctl, adr,          wdt , rdt, sts, err, len, ndn
        access(1'b0,  'x, adr, man.DAT'(wdt), rdt, sts, err,  64, ndn);
        dat = 64'(rdt);
    endtask: read64

endmodule: tcb_lite_vip_manager
