////////////////////////////////////////////////////////////////////////////////
// TCB_Lite (Tightly Coupled Bus) VIP manager model
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

module tcb_lite_vip_manager (
    // system bus interface
    tcb_lite_if.man tcb
);

    // local parameters
    localparam int unsigned DLY = tcb.DLY;
    localparam int unsigned DAT = tcb.DAT;
    localparam int unsigned ADR = tcb.ADR;
    localparam int unsigned BYT = tcb.BYT;
    localparam int unsigned SIZ = tcb.SIZ;

////////////////////////////////////////////////////////////////////////////////
// transfer request driver
////////////////////////////////////////////////////////////////////////////////

    // request initialization into idle state
    initial begin
        // idle
        tcb.vld = 1'b0;
        // request don't care
        tcb.req = '{default: 'x};
    end
    
    // request driver
    task automatic req (
        // request
        input  logic           lck = 1'b0,
        input  logic           ndn = 1'b0,
        input  logic           wen,
        input  logic [ADR-1:0] adr,
        input  logic [SIZ-1:0] siz = tcb.SIZ'($clog2(BYT)),
        input  logic [BYT-1:0] byt = '1,
        input  logic [DAT-1:0] wdt,
        // idle/backpressure timing
        input  int unsigned    idl = 0,
        output int unsigned    bpr
    );
        // cycle counter
        int unsigned cyc = 0;
        // sequence
        bpr = 0;
        do begin
            if (cyc == idl) begin
                // start handshake
                tcb.vld <= 1'b1;
                // request
                tcb.req.lck <= lck;
                tcb.req.ndn <= ndn;
                tcb.req.wen <= wen;
                tcb.req.adr <= adr;
                tcb.req.siz <= siz;
                tcb.req.byt <= byt;
                tcb.req.wdt <= wdt;
            end
            @(posedge tcb.clk);
            if (~tcb.vld) cyc++;
            if (~tcb.rdy) bpr++;
        end while (~tcb.trn);
    endtask: req

////////////////////////////////////////////////////////////////////////////////
// transfer response queue
////////////////////////////////////////////////////////////////////////////////

    // transfer response structure
    typedef tcb.rsp_t rsp_t;

    rsp_t rsp [$];

    always_ff @(posedge tcb.clk)
    begin
        if (tcb.trn_dly[DLY]) begin
            rsp.push_back(tcb.rsp);
        end
    end

////////////////////////////////////////////////////////////////////////////////
// blocking write API
////////////////////////////////////////////////////////////////////////////////

    // configuration
    // current endianness
    bit cfg_ndn;
    
    logic [DAT-1:0] tmp_dat;
    logic           tmp_err;

    initial cfg_ndn = 1'b0;

    task automatic access (
        input  logic           wen,
        input  logic [ADR-1:0] adr,
        input  logic [DAT-1:0] wdt,
        output logic [DAT-1:0] rdt,
        output logic           err,
        input  int unsigned    len = DAT,
        input  logic           ndn = cfg_ndn
    );
        // local signals
        logic [SIZ-1:0] siz = 'x;
        logic [BYT-1:0] byt = 'x;
        logic [DAT-1:0] dat = 'x;
        // logarithmic size
        if (tcb.MOD == 1'b0) begin
            siz = tcb.SIZ'($clog2(len/8));
            for (int unsigned i=0; i<len/8; i++) begin
                if (wen) begin
                    dat[8*i+:8] = wdt[8*i+:8];
                end
            end
        end
        // byte enable
        if (tcb.MOD == 1'b1) begin
            byt = '1;
            for (int unsigned i=0; i<len/8; i++) begin
                int unsigned b = i+int'(adr[$clog2(BYT)-1:0]);
                byt[  b   ] = 1'b1;
                if (wen) begin
                    dat[8*b+:8] = wdt[8*i+:8];
                end
            end
        end
        // transfer and delay
        fork
            begin: request
                int unsigned bpr;
                //   lck, ndn, wen, adr, siz, byt, wdt, idl, bpr
                req(1'b0, ndn, wen, adr, siz, byt, dat,   0, bpr);
            end: request
            begin: response
                do begin
                    @(posedge tcb.clk);
                end while (~tcb.trn_dly[DLY]);
                tmp_dat <= tcb.rsp.rdt;
                tmp_err <= tcb.rsp.err;
            end: response
        join
        // logarithmic size
        if (tcb.MOD == 1'b0) begin
            for (int unsigned i=0; i<len/8; i++) begin
                if (~wen) begin
                    rdt[8*i+:8] = tmp_dat[8*i+:8];
                end
            end
        end
        // byte enable
        if (tcb.MOD == 1'b1) begin
            byt = '1;
            for (int unsigned i=0; i<len/8; i++) begin
                int unsigned b = i+int'(adr[$clog2(BYT)-1:0]);
                if (wen) begin
                    rdt[8*i+:8] = tmp_dat[8*b+:8];
                end
            end
        end
        // error
        err = tmp_err;
    endtask: access

////////////////////////////////////////////////////////////////////////////////
// blocking write API
////////////////////////////////////////////////////////////////////////////////

    task automatic write8 (
        input  logic [DAT-1:0] adr,
        input  logic [  8-1:0] dat,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = DAT'(dat);
        logic [DAT-1:0] rdt;
        //      wen, adr, wdt, rdt, err; len, ndn
        access(1'b1, adr, wdt, rdt, err,   8, ndn);
    endtask: write8

    task automatic write16 (
        input  logic [DAT-1:0] adr,
        input  logic [ 16-1:0] dat,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = DAT'(dat);
        logic [DAT-1:0] rdt;
        //      wen, adr, wdt, rdt, err, len, ndn
        access(1'b1, adr, wdt, rdt, err,  16, ndn);
    endtask: write16

    task automatic write32 (
        input  logic [DAT-1:0] adr,
        input  logic [ 32-1:0] dat,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = DAT'(dat);
        logic [DAT-1:0] rdt;
        //      wen, adr, wdt , rdt, err, len, ndn
        access(1'b1, adr, wdt, rdt, err,  32, ndn);
    endtask: write32

    task automatic write64 (
        input  logic [DAT-1:0] adr,
        input  logic [ 64-1:0] dat,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = DAT'(dat);
        logic [DAT-1:0] rdt;
        //      wen, adr, wdt, rdt, err, len, ndn
        access(1'b1, adr, wdt, rdt, err,  64, ndn);
    endtask: write64

////////////////////////////////////////////////////////////////////////////////
// blocking read API
////////////////////////////////////////////////////////////////////////////////

    task automatic read8 (
        input  logic [DAT-1:0] adr,
        output logic [  8-1:0] dat,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = 'x;
        logic [DAT-1:0] rdt;
        //      wen, adr,      wdt , rdt, err, len, ndn
        access(1'b0, adr, DAT'(wdt), rdt, err,   8, ndn);
        dat = 8'(rdt);
    endtask: read8

    task automatic read16 (
        input  logic [DAT-1:0] adr,
        output logic [ 16-1:0] dat,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = 'x;
        logic [DAT-1:0] rdt;
        //      wen, adr,      wdt , rdt, err, len, ndn
        access(1'b0, adr, DAT'(wdt), rdt, err,  16, ndn);
        dat = 16'(rdt);
    endtask: read16

    task automatic read32 (
        input  logic [DAT-1:0] adr,
        output logic [ 32-1:0] dat,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = 'x;
        logic [DAT-1:0] rdt;
        //      wen, adr,      wdt , rdt, err, len, ndn
        access(1'b0, adr, DAT'(wdt), rdt, err,  32, ndn);
        dat = 32'(rdt);
    endtask: read32

    task automatic read64 (
        input  logic [DAT-1:0] adr,
        output logic [ 64-1:0] dat,
        output logic           err,
        input  logic           ndn = 1'b0
    );
        logic [DAT-1:0] wdt = 'x;
        logic [DAT-1:0] rdt;
        //      wen, adr,      wdt , rdt, err, len, ndn
        access(1'b0, adr, DAT'(wdt), rdt, err,  64, ndn);
        dat = 64'(rdt);
    endtask: read64

endmodule: tcb_lite_vip_manager
