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

  // transaction type (parameterized class specialization)
  typedef tcb_c #(tcb.ABW, tcb.DBW, tcb.SLW)::transaction_t transaction_t;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // response pipeline
  logic [tcb.DBW-1:0] tmp_rdy;
  logic [tcb.DBW-1:0] tmp_rdt;
  logic               tmp_err;
  logic               pip_wen [0:tcb.DLY-1];
  logic [tcb.BEW-1:0] pip_ben [0:tcb.DLY-1];
  logic [tcb.DBW-1:0] pip_rdt [0:tcb.DLY-1];
  logic               pip_err [0:tcb.DLY-1];

////////////////////////////////////////////////////////////////////////////////
// initialization
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    tcb.rdy = 1'b0;
  end

////////////////////////////////////////////////////////////////////////////////
// request/response (enable pipelined transfers with full throughput)
////////////////////////////////////////////////////////////////////////////////

  // request/response
  task automatic req_rsp (
    // request optional
    output logic               rpt,
    output logic               lck,
    // request
    output logic               wen,
    output logic [tcb.ABW-1:0] adr,
    output logic [tcb.BEW-1:0] ben,
    output logic [tcb.DBW-1:0] wdt,
    // response
    input  logic [tcb.DBW-1:0] rdt,
    input  logic               err,
    // timing idle/backpressure
    output int unsigned        idl,
    input  int unsigned        bpr
  );
    #1;
    tcb.rdy = 1'b0;
    // response
    tmp_rdt = rdt;
    tmp_err = err;
    // request
    if (bpr == 0) begin
      // ready
      tcb.rdy = 1'b1;
      // wait for transfer
      do begin
        @(posedge tcb.clk);
      end while (~tcb.trn);
    end else begin
      // backpressure
      for (int unsigned i=0; i<bpr; i+=int'(tcb.vld)) begin
        @(posedge tcb.clk);
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
    rpt = tcb.rpt;
    lck = tcb.lck;
    // request
    wen = tcb.wen;
    adr = tcb.adr;
    ben = tcb.ben;
    wdt = tcb.wdt;
  endtask: req_rsp

////////////////////////////////////////////////////////////////////////////////
// transaction sequence
////////////////////////////////////////////////////////////////////////////////

  // request/response
  task automatic sequence_driver (
    const ref transaction_t transactions_i [],
          ref transaction_t transactions_o []
  );
    for (int unsigned i=0; i<transactions_i.size(); i++) begin
      req_rsp(
        // request optional
        .rpt  (transactions_o[i].rpt),  // output
        .lck  (transactions_o[i].lck),  // output
        // request
        .wen  (transactions_o[i].wen),  // output
        .adr  (transactions_o[i].adr),  // output
        .ben  (transactions_o[i].ben),  // output
        .wdt  (transactions_o[i].wdt),  // output
        // response
        .rdt  (transactions_i[i].rdt),  // input
        .err  (transactions_i[i].err),  // input
        // timing idle/backpressure
        .idl  (transactions_o[i].idl),  // output
        .bpr  (transactions_i[i].bpr)   // input
      );
    end
  endtask: sequence_driver

////////////////////////////////////////////////////////////////////////////////
// response pipeline
////////////////////////////////////////////////////////////////////////////////

  generate
  if (tcb.DLY == 0) begin

    assign tcb.rdt = tcb.rsp ? tmp_rdt : 'x;
    assign tcb.err = tcb.rsp ? tmp_err : 'x;

  end else begin

    // TODO: try not to change "rdt" if there is no transfer
    always_ff @(posedge tcb.clk)
    if (tcb.trn) begin
      pip_wen[0] <= tcb.wen;
      pip_ben[0] <= tcb.ben;
      pip_rdt[0] <= tmp_rdt;
      pip_err[0] <= tmp_err;
    end else begin
      pip_rdt[0] <= 'x;
      pip_err[0] <= 1'bx;
    end

    for (genvar i=1; i<tcb.DLY; i++) begin

      always_ff @(posedge tcb.clk)
      begin
        pip_wen[i] <= pip_wen[i-1];
        pip_ben[i] <= pip_ben[i-1];
        pip_rdt[i] <= pip_rdt[i-1];
        pip_err[i] <= pip_err[i-1];
      end

    end

    // TODO: add byte enable
    assign tcb.rdt = tcb.rsp & ~pip_wen[tcb.DLY-1] ? pip_rdt[tcb.DLY-1] : 'x;
    assign tcb.err = tcb.rsp                       ? pip_err[tcb.DLY-1] : 'x;

  end
  endgenerate

endmodule: tcb_vip_sub