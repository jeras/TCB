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

    localparam int unsigned CTL = man.CFG.BUS.CTL;
    localparam int unsigned ADR = man.CFG.BUS.ADR;
    localparam int unsigned DAT = man.CFG.BUS.DAT;
    localparam int unsigned STS = man.CFG.BUS.STS;

    localparam int unsigned BYT = man.CFG_BUS_BYT;
    localparam int unsigned OFF = man.CFG_BUS_OFF;
    localparam int unsigned SIZ = man.CFG_BUS_SIZ;

////////////////////////////////////////////////////////////////////////////////
// transfer request queue and driver
////////////////////////////////////////////////////////////////////////////////

    // transfer request structure
    typedef man.req_t req_t;

    // transfer request queue type
    typedef struct {
        req_t        req;  // TCB request structure
        int unsigned idl;  // idle cycles number
    } req_que_t;

    // transfer request queue
    req_que_t req_que [$];

    // transfer request initialization
    initial begin
        man.vld = 1'b0;
        man.req = '{default: 'x};
    end

    // transfer request driver
    always @(req_que.size())
    begin: driver
        static int unsigned bpr = 0;
        if (req_que.size() > 0) begin
            // idle cycles
            while (req_que[0].idl > 0) begin
                @(posedge man.clk);
                req_que[0].idl--;
            end
            // drive request
            man.vld <= 1'b1;
            man.req <= req_que[0].req;
            // backpressure cycles
            do begin
                @(posedge man.clk);
                bpr++;
            end while (~man.trn);
            // remove request
            man.vld <= 1'b0;
            man.req <= '{default: 'x};
            void'(req_que.pop_front());
        end else begin
            man.vld <= 1'b0;
            man.req <= '{default: 'x};
        end
    end: driver

////////////////////////////////////////////////////////////////////////////////
// transfer response queue and sampler
////////////////////////////////////////////////////////////////////////////////

    // transfer response structure
    typedef man.rsp_t rsp_t;

    // transfer response queue type
    typedef struct {
        rsp_t        rsp;  // TCB response structure
        int unsigned bpr;  // backpressure cycles number
    } rsp_que_t;

    // transfer response queue
    rsp_que_t rsp_que [$];

    // transfer response sampler
    always_ff @(posedge man.clk)
    begin: sampler
        if (man.trn_dly[man.CFG.HSK.DLY]) begin
            rsp_que.push_back('{rsp: man.rsp, bpr: $past(driver.bpr, man.CFG.HSK.DLY)});
        end
    end: sampler

    // TODO: enable/disable transfer logger

////////////////////////////////////////////////////////////////////////////////
// blocking access API
////////////////////////////////////////////////////////////////////////////////

    // manager endianness state
    bit cfg_ndn;

    // response signals sampled
    event                       evn_rsp;
    logic [man.CFG.BUS.DAT-1:0] tmp_rdt;
    logic [man.CFG.BUS.STS-1:0] tmp_sts;
    logic                       tmp_err;

    // manager endianness state
    initial cfg_ndn = 1'b0;

    task automatic access (
        input  logic           wen,
        input  logic           ren,
        input  logic [CTL-1:0] ctl,
        input  logic [ADR-1:0] adr,
        input  logic [DAT-1:0] wdt,
        output logic [DAT-1:0] rdt,
        output logic [STS-1:0] sts,
        output logic           err,
        input  int unsigned    len = DAT/8,
        input  logic           ndn = cfg_ndn
    );
        // local signals
        logic [SIZ-1:0] siz = 'x;
        logic [BYT-1:0] byt = 'x;
        logic [DAT-1:0] dat = 'x;
        // logarithmic size
        if (man.CFG.BUS.MOD == 1'b0) begin
            siz = SIZ'($clog2(len/8));
            for (int unsigned i=0; i<len/8; i++) begin
                if (wen) begin
                    dat[8*i+:8] = wdt[8*i+:8];
                end
            end
        end
        // byte enable
        if (man.CFG.BUS.MOD == 1'b1) begin
            byt = '0;
            for (int unsigned i=0; i<len/8; i++) begin
                int unsigned b = (i+int'(adr[OFF-1:0]))%BYT;
                byt[b] = 1'b1;
                if (wen) begin
                    dat[8*b+:8] = wdt[8*i+:8];
                end
            end
        end
        // transfer and delay
        fork
            begin: request
                //                  req: '{ lck, ndn, wen, ren, ctl, adr, siz, byt, wdt}, idl
                req_que.push_back('{req: '{1'b0, ndn, wen, ren, ctl, adr, siz, byt, dat}, idl: 0});
            end: request
            begin: response
                do begin
                    @(posedge man.clk);
                end while (~man.trn_dly[man.CFG.HSK.DLY]);
                -> evn_rsp;
                tmp_rdt <= man.rsp.rdt;
                tmp_sts <= man.rsp.sts;
                tmp_err <= man.rsp.err;
                #1;  // TODO: without the unit delay, tmp_* signals do not propagate to the task output
            end: response
        join
        // logarithmic size
        if (man.CFG.BUS.MOD == 1'b0) begin
            for (int unsigned i=0; i<len/8; i++) begin
                if (ren) begin
                    rdt[8*i+:8] = tmp_rdt[8*i+:8];
                end
            end
        end
        // byte enable
        if (man.CFG.BUS.MOD == 1'b1) begin
            byt = '1;
            for (int unsigned i=0; i<len/8; i++) begin
                int unsigned b = (i+int'(adr[OFF-1:0]))%BYT;
                if (ren) begin
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
        input  logic [ADR-1:0] adr,
        input  logic [  8-1:0] dat,
        output logic [STS-1:0] sts,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = DAT'(dat);
        logic [DAT-1:0] rdt;
        //      wen, ren, ctl, adr, wdt, rdt, sts, err, len, ndn
        access(1'b1,1'b0,  'x, adr, wdt, rdt, sts, err,   8, ndn);
    endtask: write8

    task automatic write16 (
        input  logic [ADR-1:0] adr,
        input  logic [ 16-1:0] dat,
        output logic [STS-1:0] sts,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = DAT'(dat);
        logic [DAT-1:0] rdt;
        //      wen, ren, ctl, adr, wdt, rdt, sts, err, len, ndn
        access(1'b1,1'b0,  'x, adr, wdt, rdt, sts, err,  16, ndn);
    endtask: write16

    task automatic write32 (
        input  logic [ADR-1:0] adr,
        input  logic [ 32-1:0] dat,
        output logic [STS-1:0] sts,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = DAT'(dat);
        logic [DAT-1:0] rdt;
        //      wen, ren, ctl, adr, wdt, rdt, sts, err, len, ndn
        access(1'b1,1'b0,  'x, adr, wdt, rdt, sts, err,  32, ndn);
    endtask: write32

    task automatic write64 (
        input  logic [ADR-1:0] adr,
        input  logic [ 64-1:0] dat,
        output logic [STS-1:0] sts,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = DAT'(dat);
        logic [DAT-1:0] rdt;
        //      wen, ren, ctl, adr, wdt, rdt, sts, err, len, ndn
        access(1'b1,1'b0,  'x, adr, wdt, rdt, sts, err,  64, ndn);
    endtask: write64

////////////////////////////////////////////////////////////////////////////////
// blocking read API
////////////////////////////////////////////////////////////////////////////////

    task automatic read8 (
        input  logic [ADR-1:0] adr,
        output logic [  8-1:0] dat,
        output logic [STS-1:0] sts,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = 'x;
        logic [DAT-1:0] rdt;
        //      wen, ren, ctl, adr,      wdt , rdt, sts, err, len, ndn
        access(1'b0,1'b1,  'x, adr, DAT'(wdt), rdt, sts, err,   8, ndn);
        dat = 8'(rdt);
    endtask: read8

    task automatic read16 (
        input  logic [ADR-1:0] adr,
        output logic [ 16-1:0] dat,
        output logic [STS-1:0] sts,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = 'x;
        logic [DAT-1:0] rdt;
        //      wen, ren, ctl, adr,      wdt , rdt, sts, err, len, ndn
        access(1'b0,1'b1,  'x, adr, DAT'(wdt), rdt, sts, err,  16, ndn);
        dat = 16'(rdt);
    endtask: read16

    task automatic read32 (
        input  logic [ADR-1:0] adr,
        output logic [ 32-1:0] dat,
        output logic [STS-1:0] sts,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = 'x;
        logic [DAT-1:0] rdt;
        //      wen, ren, ctl, adr,      wdt , rdt, sts, err, len, ndn
        access(1'b0,1'b1,  'x, adr, DAT'(wdt), rdt, sts, err,  32, ndn);
        dat = 32'(rdt);
    endtask: read32

    task automatic read64 (
        input  logic [DAT-1:0] adr,
        output logic [ 64-1:0] dat,
        output logic [STS-1:0] sts,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = 'x;
        logic [DAT-1:0] rdt;
        //      wen, ren, ctl, adr,      wdt , rdt, sts, err, len, ndn
        access(1'b0,1'b1,  'x, adr, DAT'(wdt), rdt, sts, err,  64, ndn);
        dat = 64'(rdt);
    endtask: read64

endmodule: tcb_lite_vip_manager
