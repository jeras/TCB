////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verifivation IP) subordinate
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
#(
  // bus widths
  int unsigned AW = 32,     // address     width
  int unsigned DW = 32,     // data        width
  int unsigned SW =     8,  // selection   width
  int unsigned BW = DW/SW,  // byte enable width
  // response delay
  int unsigned DLY = 1
)(
  // system bus
  tcb_if.sub bus
);

generate
if (DLY != bus.DLY)  $error("%m parameter DLY validation failed");
endgenerate

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // response pipeline
  logic [DW-1:0] tmp_rdt;
  logic          tmp_err;
  logic [DW-1:0] pip_rdt [0:DLY-1];
  logic          pip_err [0:DLY-1];

////////////////////////////////////////////////////////////////////////////////
// request/response (enable pipelined transfers with full throughput)
////////////////////////////////////////////////////////////////////////////////

  // request
  task req (
    output logic          wen,
    output logic [AW-1:0] adr,
    output logic [BW-1:0] ben,
    output logic [DW-1:0] wdt,
    output logic          lck,
    output logic          rpt
  );
    // check for backpressure
    do begin
      @(posedge bus.clk);
    end while (~bus.rdy);
    // idle
    wen = bus.wen;
    adr = bus.adr;
    ben = bus.ben;
    wdt = bus.wdt;
    lck = bus.lck;
    rpt = bus.rpt;
  endtask: req

  // response
  task rsp (
    // bus signals
    input  logic [DW-1:0] rdt,
    input  logic          err,
    // timing
    input  int            tmg = 0
  );
    // idle
    repeat (tmg) @(posedge bus.clk);
    // response
    #1;
    tmp_rdt = rdt;
    tmp_err = err;
    // ready
    bus.rdy = 1'b1;
    @(posedge bus.clk);
    #1;
    bus.rdy = 1'b1;
  endtask: rsp

////////////////////////////////////////////////////////////////////////////////
// response pipeline
////////////////////////////////////////////////////////////////////////////////

  generate
  if (DLY == 0) begin

    assign bus.rdt = tmp_rdt;
    assign bus.err = tmp_err;

  end else  begin

    always_ff @(posedge bus.clk)
    if (bus.trn) begin
      pip_rdt[0] <= tmp_rdt;
      pip_err[0] <= tmp_err;
    end

    assign bus.rdt = pip_rdt[DLY-1];
    assign bus.err = pip_err[DLY-1];

  end
  endgenerate

endmodule: tcb_vip_sub