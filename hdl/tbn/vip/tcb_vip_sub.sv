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

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // response pipeline
  logic [tcb.DW-1:0] tmp_rdt;
  logic              tmp_err;
  logic [tcb.DW-1:0] pip_rdt [0:tcb.DLY-1];
  logic              pip_err [0:tcb.DLY-1];

////////////////////////////////////////////////////////////////////////////////
// request/response (enable pipelined transfers with full throughput)
////////////////////////////////////////////////////////////////////////////////

  // request
  task req (
    output logic              wen,
    output logic [tcb.AW-1:0] adr,
    output logic [tcb.BW-1:0] ben,
    output logic [tcb.DW-1:0] wdt,
    output logic              lck,
    output logic              rpt
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
    input  logic [tcb.DW-1:0] rdt,
    input  logic              err,
    // timing
    input  int                tmg = 0
  );
    // idle
    repeat (tmg) @(posedge tcb.clk);
    // response
    #1;
    tmp_rdt = rdt;
    tmp_err = err;
    // ready
    tcb.rdy = 1'b1;
    @(posedge tcb.clk);
    #1;
    tcb.rdy = 1'b1;
  endtask: rsp

////////////////////////////////////////////////////////////////////////////////
// response pipeline
////////////////////////////////////////////////////////////////////////////////

  generate
  if (tcb.DLY == 0) begin

    assign tcb.rdt = tmp_rdt;
    assign tcb.err = tmp_err;

  end else  begin

    always_ff @(posedge tcb.clk)
    if (tcb.trn) begin
      pip_rdt[0] <= tmp_rdt;
      pip_err[0] <= tmp_err;
    end

    assign tcb.rdt = pip_rdt[tcb.DLY-1];
    assign tcb.err = pip_err[tcb.DLY-1];

  end
  endgenerate

endmodule: tcb_vip_sub