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

////////////////////////////////////////////////////////////////////////////////
// request/response (enable pipelined transfers with full throughput)
////////////////////////////////////////////////////////////////////////////////

  initial  tcb.vld = 1'b0;

  // request
  task req (
    // request
    input  logic               wen,
    input  logic [tcb.ABW-1:0] adr,
    input  logic [tcb.BEW-1:0] ben,
    input  logic [tcb.DBW-1:0] wdt,
    // request optional
    input  logic               lck = 1'b0,
    input  logic               rpt = 1'b0,
    // timing idle
    input  int unsigned        idl = 0
  );
    // request timing
    repeat (idl) @(posedge tcb.clk);
    // drive transfer
    #1;
    // hanshake
    tcb.vld = 1'b1;
    // request
    tcb.wen = wen;
    tcb.adr = adr;
    tcb.ben = ben;
    tcb.wdt = wdt;
    // request optional
    tcb.lck = lck;
    tcb.rpt = rpt;
    // backpressure
    do begin
      @(posedge tcb.clk);
    end while (~tcb.rdy);
    // drive idle/undefined
    #1;
    // handshake
    tcb.vld = 1'b0;
    // request
    tcb.wen = 'x;
    tcb.adr = 'x;
    tcb.ben = 'x;
    tcb.wdt = 'x;
    // request optional
    tcb.lck = 'x;
    tcb.rpt = 'x;
  endtask: req

  // response task
  task rsp (
    output logic [tcb.DBW-1:0] rdt,
    output logic               err
  );
    // response delay
    if (tcb.DLY > 0) begin
      do begin
        @(posedge tcb.clk);
      end while (~tcb.rsp);
    end
    // response
    rdt = tcb.rdt;
    err = tcb.err;
  endtask: rsp

////////////////////////////////////////////////////////////////////////////////
// generic read/write (waits for response after each request)
////////////////////////////////////////////////////////////////////////////////

  // generic write
  task write (
    // request
    input  logic [tcb.ABW-1:0] adr,
    input  logic [tcb.BEW-1:0] ben,
    input  logic [tcb.DBW-1:0] dat,
    // response
    output logic               err,
    // request optional
    input  logic               lck = 1'b0,
    input  logic               rpt = 1'b0
  );
    // ignored value
    logic [tcb.DBW-1:0] rdt;
    // request
    req (
      .wen (1'b1),
      .adr (adr),
      .ben (ben),
      .wdt (dat),
      .lck (lck),
      .rpt (rpt)
    );
    // response
    rsp (
      .rdt (rdt),
      .err (err)
    );
  endtask: write

  // generic read
  task read (
    // request
    input  logic [tcb.ABW-1:0] adr,
    input  logic [tcb.BEW-1:0] ben,
    output logic [tcb.DBW-1:0] dat,
    // response
    output logic               err,
    // request optional
    input  logic               lck = 1'b0,
    input  logic               rpt = 1'b0
  );
    // request
    req (
      .wen (1'b0),
      .adr (adr),
      .ben (ben),
      .wdt ('x),
      .lck (lck),
      .rpt (rpt)
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

endmodule: tcb_vip_man