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
  tcb_if tcb
);

  // response pipeline
  logic [tcb.DBW-1:0] tmp_rdt;
  logic               tmp_err;
  logic [tcb.DBW-1:0] pip_rdt [0:tcb.DLY-1];
  logic               pip_err [0:tcb.DLY-1];

  // request
  task req (
    output logic               wen,
    output logic [tcb.ABW-1:0] adr,
    output logic [tcb.BEW-1:0] ben,
    output logic [tcb.DBW-1:0] wdt,
    output logic               lck,
    output logic               rpt
  );
    // check for backpressure
    do begin
      @(posedge tcb.clk);
    end while (~tcb.rdy);
    // idle
    wen = tcb.wen;
    adr = tcb.adr;
    ben = tcb.ben;
    wdt = tcb.wdt;
    lck = tcb.lck;
    rpt = tcb.rpt;
  endtask: req

  // response
  task rsp (
    // tcb signals
    input  logic [tcb.DBW-1:0] rdt,
    input  logic               err,
    // timing
    input  int unsigned        tmg = 0
  );
    // response
    tmp_rdt = rdt;
    tmp_err = err;
    if (tmg == 0) begin
      // ready
      tcb.rdy = 1'b1;
      // wait for transfer
      do begin
        @(posedge tcb.clk);
      end while (~tcb.trn);
    end
    // idle
    #1;
    tmp_rdt = 'x;
    tmp_err = 'x;
  endtask: rsp

  generate
  if (tcb.DLY == 0) begin

    initial begin
      $display("tcb.DLY == 0: DLY = %d", tcb.DLY);
    end

    assign tcb.rdt = tcb.rsp ? tmp_rdt : 'x;
    assign tcb.err = tcb.rsp ? tmp_err : 'x;

  end else begin

    initial begin
      $display("else: DLY = %d", tcb.DLY);
    end

    always_ff @(posedge tcb.clk)
    if (tcb.trn) begin
      pip_rdt[0] <= tmp_rdt;
      pip_err[0] <= tmp_err;
    end else begin
      pip_rdt[0] <= 'x;
      pip_err[0] <= 1'bx;
    end

    for (genvar i=1; i<tcb.DLY; i++) begin

      initial begin
        $display("for: DLY = %d, genvar i = %d", tcb.DLY, i);
      end

      always_ff @(posedge tcb.clk)
      begin
        // --Verilator debug line
        $display("DLY = %d, genvar i = %d", tcb.DLY, i);
        pip_rdt[i] <= pip_rdt[i-1];
        pip_err[i] <= pip_err[i-1];
      end

    end

    assign tcb.rdt = tcb.rsp ? pip_rdt[tcb.DLY-1] : 'x;
    assign tcb.err = tcb.rsp ? pip_err[tcb.DLY-1] : 'x;

  end
  endgenerate

endmodule: tcb_vip_sub