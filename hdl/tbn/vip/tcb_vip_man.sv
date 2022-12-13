////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verifivation IP) MANager
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

module tcb_vip_man
  import tcb_vip_pkg::*;
(
  // TCB interface
  tcb_if.man tcb
);

  // parameterized class specialization
  typedef tcb_c #(tcb.ABW, tcb.DBW, tcb.SLW) tcb_s;

////////////////////////////////////////////////////////////////////////////////
// initialization
////////////////////////////////////////////////////////////////////////////////

  // initialize to idle state
  initial  tcb.vld = 1'b0;

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
    tcb.rpt = seq.rpt;
    tcb.lck = seq.lck;
    // request
    tcb.wen = seq.wen;
    tcb.adr = seq.adr;
    tcb.ben = seq.ben;
    tcb.wdt = seq.wdt;
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
    end while (~tcb.rsp);
    // response
    seq.rdt = tcb.rdt;
    seq.err = tcb.err;
  endtask: rsp_lsn

////////////////////////////////////////////////////////////////////////////////
// transaction sequence
////////////////////////////////////////////////////////////////////////////////

  int unsigned req_i;
  int unsigned rsp_i;

  // request/response
  task automatic sequencer (
    inout  tcb_s::transaction_t transactions []
  );
    $display("DEBUG: transactions.size = %d", transactions.size);
    fork
      begin: fork_req_drv
//        foreach (transactions[i])  req_drv(transactions[i]);
        foreach (transactions[i]) begin
          req_i = i;
          req_drv(transactions[i]);
        end
        $display("DEBUG: END of manager request");
      end: fork_req_drv
      begin: fork_rsp_lsn
        // TODO: maybe put a response delay here
        //repeat(tcb.DLY) @(posedge clk);
//        foreach (transactions[i])  rsp_lsn(transactions[i]);
        foreach (transactions[i]) begin
          rsp_i = i;
          rsp_lsn(transactions[i]);
        end
        $display("DEBUG: END of manager response");
      end: fork_rsp_lsn
    join
  endtask: sequencer

////////////////////////////////////////////////////////////////////////////////
// BFM (Bus Functional Model) (emulates a RISC-V manager)
////////////////////////////////////////////////////////////////////////////////

  // read/write access of any size
  task automatic access (
    // data length
    input  int unsigned        len,
    // request
    input  logic               wen,
    input  logic [tcb.ABW-1:0] adr,
    ref    logic [tcb.SLW-1:0] dat [],
    // response
    output logic               err
  );
    int unsigned num;
    tcb_s::transaction_t transactions [];
    int unsigned idx_trn = 0;
    int unsigned idx_ben = adr % tcb.BEW;
    // the number of transactions is
    // = the access length + missalligned part of the address
    // / divided by bus native byte enable width
    // + plus one, if there is a reinder to the division.
    num = len + adr % tcb.BEW;
    num = (num / tcb.BEW) + ((num % tcb.BEW) ? 1 : 0);
    // local transactions
    transactions = new[num];
    $display("Transaction starts here.");
    // mapping
    transactions = '{default: tcb_s::TRANSACTION_INIT};
    for (int unsigned i=0; i<len; i++) begin
      // request optional
      transactions[idx_trn].rpt = 1'b0;
      transactions[idx_trn].lck = (idx_trn < num) ? 1'b1 : 1'b0;
      // request
      transactions[idx_trn].wen = wen;
      transactions[idx_trn].adr = adr + idx_trn * tcb.BEW;
      transactions[idx_trn].ben[idx_ben] = 1'b1;
      transactions[idx_trn].wdt[idx_ben] = dat[i];
      // timing idle/backpressure
      transactions[idx_trn].idl = 0;
      // index increments
      idx_ben = (idx_ben + 1) % tcb.BEW;
      if (idx_ben == 0) idx_trn++;
    end
    // transaction
    sequencer(transactions);
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

endmodule: tcb_vip_man