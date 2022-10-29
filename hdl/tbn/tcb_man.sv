////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus manager
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

module tcb_man
  import tcb_pkg::*;
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
  tcb_if.man bus
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

generate
  if (DLY != bus.DLY)  $error("ERROR: %m parameter DLY checker failed");
endgenerate

////////////////////////////////////////////////////////////////////////////////
// request/response (enable pipelined transfers with full throughput)
////////////////////////////////////////////////////////////////////////////////

  initial  bus.vld = 1'b0;

  // request
  task req (
    input  logic          wen,
    input  logic [AW-1:0] adr,
    input  logic [BW-1:0] ben,
    input  logic [DW-1:0] wdt,
    input  logic          lck = 1'b0,
    input  logic          rpt = 1'b0,
    // timing
    input  int            tmg = 0
  );
    // idle
    repeat (tmg) @(posedge bus.clk);
    // request
    #1;
    bus.vld = 1'b1;
    bus.wen = wen;
    bus.adr = adr;
    bus.ben = ben;
    bus.wdt = wdt;
    bus.lck = lck;
    bus.rpt = rpt;
    // backpressure
    do begin
      @(posedge bus.clk);
    end while (~bus.rdy);
    // idle
    #1;
    bus.vld = 1'b0;
    bus.wen = 'x;
    bus.adr = 'x;
    bus.ben = 'x;
    bus.wdt = 'x;
    bus.lck = 'x;
    bus.rpt = 'x;
  endtask: req

  // response
  task rsp (
    output logic [DW-1:0] rdt,
    output logic          err
  );
    // response delay
    do begin
      @(posedge bus.clk);
    end while (~bus.rsp);
    // response
    rdt = bus.rdt;
    err = bus.err;
  endtask: rsp

////////////////////////////////////////////////////////////////////////////////
// generic read/write (waits for response after each request)
////////////////////////////////////////////////////////////////////////////////

  // generic write
  task write (
    input  logic [AW-1:0] adr,
    input  logic [BW-1:0] ben,
    input  logic [DW-1:0] dat,
    output logic          err
  );
    // ignored value
    logic [DW-1:0] rdt;
    // request
    req (
      .wen (1'b1),
      .adr (adr),
      .ben (ben),
      .wdt (dat),
      .lck (1'b0),
      .rpt (1'b0)
    );
    // response
    rsp (
      .rdt (rdt),
      .err (err)
    );
  endtask: write

  // generic read
  task read (
    input  logic [AW-1:0] adr,
    input  logic [BW-1:0] ben,
    output logic [DW-1:0] dat,
    output logic          err
  );
    // request
    req (
      .wen (1'b0),
      .adr (adr),
      .ben (ben),
      .wdt ('x),
      .lck (1'b0),
      .rpt (1'b0)
    );
    // response
    rsp (
      .rdt (dat),
      .err (err)
    );
  endtask: read

////////////////////////////////////////////////////////////////////////////////
// BFM (Bus Functional Model) (emulates a RISC-V manager)
////////////////////////////////////////////////////////////////////////////////

// write64
// write32
// write16
// write8
// read64
// read32
// read16
// read8

endmodule: tcb_man