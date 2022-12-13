////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verifivation IP) SUBordinate
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

module tcb_vip_sub
  import tcb_vip_pkg::*;
(
  // TCB interface
  tcb_if.sub tcb
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

  // initialize to idle state
  initial  tcb.rdy = 1'b0;

////////////////////////////////////////////////////////////////////////////////
// request/response (enable pipelined transactions with full throughput)
////////////////////////////////////////////////////////////////////////////////

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
    seq.rpt = tcb.rpt;
    seq.lck = tcb.lck;
    // request
    seq.wen = tcb.wen;
    seq.adr = tcb.adr;
    seq.ben = tcb.ben;
    seq.wdt = tcb.wdt;
  endtask: req_lsn

  // response driver
  task automatic rsp_drv (
    inout  tcb_s::transaction_t seq
  );
    // response
    tmp_rdt = seq.rdt;
    tmp_err = seq.err;
    // wait for response
    do begin
      @(posedge tcb.clk);
    end while (~tcb.rsp);
  endtask: rsp_drv

  // response signal driver
  assign tcb.rdt = tcb.rsp ? tmp_rdt : 'x;
  assign tcb.err = tcb.rsp ? tmp_err : 'x;

////////////////////////////////////////////////////////////////////////////////
// transaction sequence
////////////////////////////////////////////////////////////////////////////////

  // request/response
  task automatic sequencer (
    inout  tcb_s::transaction_t transactions []
  );
    fork
      begin: fork_req_lsn
        foreach (transactions[i])  req_lsn(transactions[i]);
      end: fork_req_lsn
      begin: fork_rsp_drv
        // response delay to avoid interfering with previous sequence
        repeat(tcb.DLY) @(posedge tcb.clk);
        foreach (transactions[i])  rsp_drv(transactions[i]);
      end: fork_rsp_drv
    join
  endtask: sequencer

endmodule: tcb_vip_sub