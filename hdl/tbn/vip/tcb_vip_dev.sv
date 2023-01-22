////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verifivation IP) device
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

module tcb_vip_dev
  import tcb_pkg::*;
  import tcb_vip_pkg::*;
#(
  string MODE = "MON"  // supported modes are MAN/MON/SUB/MEM
)(
  // TCB interface (without modport constraints)
  tcb_if tcb
);

  // parameterized class specialization
  typedef tcb_c #(tcb.ABW, tcb.DBW, tcb.SLW) tcb_s;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // response pipeline
  logic [tcb.DBW-1:0] tmp_rdt;
  logic               tmp_err;

////////////////////////////////////////////////////////////////////////////////
// initialization
////////////////////////////////////////////////////////////////////////////////

  generate
  case (MODE)
    // manager
    "MAN": begin
      // initialize to idle state
      initial  tcb.vld = 1'b0;
    end
    // monitor
    "MON": begin
    end
    // subordinate
    "SUB": begin
      // initialize to idle state
      initial  tcb.rdy = 1'b0;
    end
    // memory
    "MEM": begin
      // trivial always ready
      assign  tcb.rdy = 1'b1;
    end
  endcase
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// request/response (enable pipelined transactions with full throughput)
////////////////////////////////////////////////////////////////////////////////

  // request driver
  task automatic req_drv (
    inout  tcb_s::transaction_t seq
  );
    // request timing
    repeat (seq.idl) @(posedge tcb.clk);
    // drive transfer
    #1;
    // hanshake
    tcb.vld = 1'b1;
    // request optional
    tcb.inc = seq.req.inc;
    tcb.rpt = seq.req.rpt;
    tcb.lck = seq.req.lck;
    // request
    tcb.wen = seq.req.wen;
    tcb.adr = seq.req.adr;
    tcb.ben = seq.req.ben;
    tcb.wdt = seq.req.wdt;
    // backpressure
    seq.bpr = 0;
    do begin
      @(posedge tcb.clk);
      if (~tcb.rdy) seq.bpr++;
    end while (~tcb.trn);
    // drive idle/undefined
    #1;
    // handshake
    tcb.vld = 1'b0;
    // request optional
    tcb.inc = 'x;
    tcb.rpt = 'x;
    tcb.lck = 'x;
    // request
    tcb.wen = 'x;
    tcb.adr = 'x;
    tcb.ben = 'x;
    tcb.wdt = 'x;
  endtask: req_drv

  // response listener
  task automatic rsp_lsn (
    inout  tcb_s::transaction_t seq
  );
    // wait for response
    do begin
      @(posedge tcb.clk);
    end while (~tcb.rsp[tcb.DLY]);
    // response
    seq.rsp.rdt = tcb.rdt;
    seq.rsp.err = tcb.err;
  endtask: rsp_lsn

  // request listener
  task automatic req_lsn (
    inout  tcb_s::transaction_t seq
  );
    #1;
    tcb.rdy = 1'b0;
    // TODO: mesure idle time
    seq.idl = 0;
    // request
    if (seq.bpr == 0) begin
      // ready
      tcb.rdy = 1'b1;
      // wait for transfer
      do begin
        @(posedge tcb.clk);
        seq.idl += tcb.vld ? 0 : 1;
      end while (~tcb.trn);
    end else begin
      // backpressure
      for (int unsigned i=0; i<seq.bpr; i+=(tcb.vld?1:0)) begin
        @(posedge tcb.clk);
        seq.idl += tcb.vld ? 0 : 1;
      end
      // ready
      #1;
      tcb.rdy = 1'b1;
      // wait for transfer
      do begin
        @(posedge tcb.clk);
      end while (~tcb.trn);
    end
    // request optional
    seq.req.inc = tcb.inc;
    seq.req.rpt = tcb.rpt;
    seq.req.lck = tcb.lck;
    // request
    seq.req.wen = tcb.wen;
    seq.req.adr = tcb.adr;
    seq.req.siz = tcb.siz;
    seq.req.ben = tcb.ben;
    seq.req.wdt = tcb.wdt;
  endtask: req_lsn

  // response driver
  task automatic rsp_drv (
    inout  tcb_s::transaction_t seq
  );
    // response
    tmp_rdt = seq.rsp.rdt;
    tmp_err = seq.rsp.err;
    // wait for response
    do begin
      @(posedge tcb.clk);
    end while (~tcb.rsp[tcb.DLY]);
  endtask: rsp_drv

  generate
  if (MODE == "SUB") begin
    // response signal driver
    assign tcb.rdt = tcb.rsp[tcb.DLY] ? tmp_rdt : 'x;
    assign tcb.err = tcb.rsp[tcb.DLY] ? tmp_err : 'x;
  end
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// transaction sequence non-blocking API
////////////////////////////////////////////////////////////////////////////////

  // request/response
  task automatic sequencer (
    inout  tcb_s::transactions_t transactions
  );
    fork
      begin: fork_req
        foreach (transactions[i]) begin
          case (MODE)
            "MAN": req_drv(transactions[i]);
            "MON": req_lsn(transactions[i]);
            "SUB": req_lsn(transactions[i]);
          endcase 
        end
      end: fork_req
      begin: fork_rsp
        foreach (transactions[i]) begin
          case (MODE)
            "MAN": rsp_lsn(transactions[i]);
            "MON": rsp_lsn(transactions[i]);
            "SUB": rsp_drv(transactions[i]);
          endcase 
        end
      end: fork_rsp
    join
  endtask: sequencer

////////////////////////////////////////////////////////////////////////////////
// BFM (Bus Functional Model) blocking API (emulates a RISC-V manager)
////////////////////////////////////////////////////////////////////////////////

  // read/write access of any size
  task automatic access (
    // data size
    input  int unsigned        siz,
    // request
    input  logic               wen,
    input  logic [tcb.ABW-1:0] adr,
    ref    logic [tcb.SLW-1:0] dat [],
    // response
    output logic               err,
    // mode
    input  tcb_mode_t          mode = '{device: TCB_MEMORY, endian: TCB_LITTLE, order: TCB_ASCENDING}
  );
    int unsigned num;
    tcb_s::transactions_t transactions;
    // TODO: check if missalligned access is supported
    //if (tcb.MIS)

        // number of transactions
        num = (siz / tcb.BEW);
        transactions = new[num];
//        $display("Transaction start.");
        // mapping
        transactions = '{default: tcb_s::TRANSACTION_INIT};
        for (int unsigned i=0; i<num; i++) begin
          // request optional
          transactions[i].req.inc = 1'b0;
          transactions[i].req.rpt = 1'b0;
          transactions[i].req.lck = (i == num) ? 1'b0 : 1'b1;
          // request
          transactions[i].req.wen = wen;
          transactions[i].req.adr = adr + i * tcb.BEW;
          for (int unsigned b=0; b<tcb.BEW; b++) begin
            transactions[i].req.ben[b] = 1'b1;
            transactions[i].req.wdt[b] = dat[b + i * tcb.BEW];
          end
          // timing idle (no backpressure)
          transactions[i].idl = 0;
        end
      //end
    //endcase
    // transaction
    sequencer(transactions);
    // response
    err = 1'b0;
    for (int unsigned i=0; i<num; i++) begin
      for (int unsigned b=0; b<tcb.BEW; b++) begin
        dat[b + i * tcb.BEW] = transactions[i].rsp.rdt[b];
        err                 |= transactions[i].rsp.err;
      end
    end
  endtask: access

////////////////////////////////////////////////////////////////////////////////
// native data width read/write (waits for response after each request)
////////////////////////////////////////////////////////////////////////////////

//// write64
//// write32
// write16
// write8
// read64
// read32
// read16
// read8

  task write (
    // request
    input  logic              [tcb.ABW-1:0] adr,
    input  logic [tcb.BEW-1:0][tcb.SLW-1:0] wdt,
    // response
    output logic                            err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[tcb.BEW];
    for (int unsigned i=0; i<tcb.BEW; i++)  dat[i] = wdt[i];
    //          siz,  wen, adr, dat, err
    access (tcb.BEW, 1'b1, adr, dat, err);
  endtask: write

  task read (
    // request
    input  logic              [tcb.ABW-1:0] adr,
    // response
    output logic [tcb.BEW-1:0][tcb.SLW-1:0] rdt,
    output logic                            err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[tcb.BEW];
    //          siz,  wen, adr, dat, err
    access (tcb.BEW, 1'b0, adr, dat, err);
    for (int unsigned i=0; i<tcb.BEW; i++)  rdt[i] = dat[i];
  endtask: read

  task write8 (
    input  logic        [tcb.ABW-1:0] adr,
    input  logic [1-1:0][tcb.SLW-1:0] wdt,
    output logic                      err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[1];
    for (int unsigned i=0; i<1; i++)  dat[i] = wdt[i];
    access (1, 1'b1, adr, dat, err);
  endtask: write8

  task read8 (
    input  logic        [tcb.ABW-1:0] adr,
    output logic [1-1:0][tcb.SLW-1:0] rdt,
    output logic                      err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[1];
    access (1, 1'b0, adr, dat, err);
    for (int unsigned i=0; i<1; i++)  rdt[i] = dat[i];
  endtask: read8

  task write16 (
    input  logic        [tcb.ABW-1:0] adr,
    input  logic [2-1:0][tcb.SLW-1:0] wdt,
    output logic                      err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[2];
    for (int unsigned i=0; i<2; i++)  dat[i] = wdt[i];
    access (2, 1'b1, adr, dat, err);
  endtask: write16

  task read16 (
    input  logic        [tcb.ABW-1:0] adr,
    output logic [2-1:0][tcb.SLW-1:0] rdt,
    output logic                      err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[2];
    access (2, 1'b0, adr, dat, err);
    for (int unsigned i=0; i<2; i++)  rdt[i] = dat[i];
  endtask: read16

  task write32 (
    input  logic        [tcb.ABW-1:0] adr,
    input  logic [4-1:0][tcb.SLW-1:0] wdt,
    output logic                      err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[4];
    for (int unsigned i=0; i<4; i++)  dat[i] = wdt[i];
    access (4, 1'b1, adr, dat, err);
  endtask: write32

  task read32 (
    input  logic        [tcb.ABW-1:0] adr,
    output logic [4-1:0][tcb.SLW-1:0] rdt,
    output logic                      err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[4];
    access (4, 1'b0, adr, dat, err);
    for (int unsigned i=0; i<4; i++)  rdt[i] = dat[i];
  endtask: read32

  task write64 (
    input  logic        [tcb.ABW-1:0] adr,
    input  logic [8-1:0][tcb.SLW-1:0] wdt,
    output logic                      err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[8];
    for (int unsigned i=0; i<8; i++)  dat[i] = wdt[i];
    access (8, 1'b1, adr, dat, err);
  endtask: write64

  task read64 (
    input  logic        [tcb.ABW-1:0] adr,
    output logic [8-1:0][tcb.SLW-1:0] rdt,
    output logic                      err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[8];
    access (8, 1'b0, adr, dat, err);
    for (int unsigned i=0; i<8; i++)  rdt[i] = dat[i];
  endtask: read64

  task write128 (
    input  logic         [tcb.ABW-1:0] adr,
    input  logic [16-1:0][tcb.SLW-1:0] wdt,
    output logic                       err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[16];
    for (int unsigned i=0; i<16; i++)  dat[i] = wdt[i];
    access (16, 1'b1, adr, dat, err);
  endtask: write128

  task read128 (
    input  logic         [tcb.ABW-1:0] adr,
    output logic [16-1:0][tcb.SLW-1:0] rdt,
    output logic                       err
  );
    logic [tcb.SLW-1:0] dat [];
    dat = new[16];
    access (16, 1'b0, adr, dat, err);
    for (int unsigned i=0; i<16; i++)  rdt[i] = dat[i];
  endtask: read128

endmodule: tcb_vip_dev