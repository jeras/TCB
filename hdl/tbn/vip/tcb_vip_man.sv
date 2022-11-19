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

  // initialize to idle state
  initial  tcb.vld = 1'b0;

  // request
  task automatic req (
    // request optional
    input  logic               rpt,
    input  logic               lck,
    // request
    input  logic               wen,
    input  logic [tcb.ABW-1:0] adr,
    input  logic [tcb.BEW-1:0] ben,
    input  logic [tcb.DBW-1:0] wdt,
    // timing idle/backpressure
    input  int unsigned        idl,
    output int unsigned        bpr
  );
    // request timing
    repeat (idl) @(posedge tcb.clk);
    // drive transfer
    #1;
    // hanshake
    tcb.vld = 1'b1;
    // request optional
    tcb.rpt = rpt;
    tcb.lck = lck;
    // request
    tcb.wen = wen;
    tcb.adr = adr;
    tcb.ben = ben;
    tcb.wdt = wdt;
    // backpressure
    bpr = 0;
    do begin
      @(posedge tcb.clk);
      if (~tcb.rdy) bpr++;
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
  endtask: req

  // response task
  task automatic rsp (
    output logic [tcb.DBW-1:0] rdt,
    output logic               err
  );
    do begin
      @(posedge tcb.clk);
    end while (~tcb.trn);
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
// BFM (Bus Functional Model) (emulates a RISC-V manager)
////////////////////////////////////////////////////////////////////////////////

  // native write
  task automatic transaction (
    // request optional
    input  logic               rpt,
    input  logic               lck,
    // data length
    input  int unsigned        len,
    // request
    input  logic               wen,
    input  logic [tcb.ABW-1:0] adr,
    ref    logic [tcb.SLW-1:0] dat [],
    // response
    output logic               err,
    // timing idle/backpressure
    input  int unsigned        idl,
    output int unsigned        bpr
  );
    // local signals
    logic [tcb.BEW-1:0]              ben = '0;
    logic [tcb.BEW-1:0][tcb.SLW-1:0] wdt;
    logic [tcb.BEW-1:0][tcb.SLW-1:0] rdt;
    $display("Transaction starts here.");
    // mapping
    for (int unsigned i=0; i<len; i++) begin
      ben = '1;
      wdt[i] = dat[i];
    end
    // transaction
    fork
      begin
        $display("Request expected here.");
        // request
        req (
          .rpt (rpt),
          .lck (lck),
          .wen (wen),
          .adr (adr),
          .ben (ben),
          .wdt (wdt),
          .idl (idl),
          .bpr (bpr)
        );
      end
      begin
        // response
        rsp (
          .rdt (rdt),
          .err (err)
        );
      end
    join
    // mapping
    for (int unsigned i=0; i<len; i++) begin
      dat[i] = rdt[i];
    end
  endtask: transaction

////////////////////////////////////////////////////////////////////////////////
// native data width read/write (waits for response after each request)
////////////////////////////////////////////////////////////////////////////////

//  // native write
//  task write (
//    // request
//    input  logic [tcb.ABW-1:0] adr,
//    input  logic [tcb.BEW-1:0] ben,
//    input  logic [tcb.DBW-1:0] dat,
//    // response
//    output logic               err
//  );
//    // ignored value
//    logic [tcb.DBW-1:0] rdt;
//    // request
//    req (
//      .rpt (1'b0),
//      .lck (1'b0),
//      .wen (1'b1),
//      .adr (adr),
//      .ben (ben),
//      .wdt (dat)
//    );
//    // response
//    rsp (
//      .rdt (rdt),
//      .err (err)
//    );
//  endtask: write
//
//  // native read
//  task read (
//    // request
//    input  logic [tcb.ABW-1:0] adr,
//    input  logic [tcb.BEW-1:0] ben,
//    output logic [tcb.DBW-1:0] dat,
//    // response
//    output logic               err
//  );
//    // request
//    req (
//      .rpt (1'b0),
//      .lck (1'b0),
//      .wen (1'b0),
//      .adr (adr),
//      .ben (ben),
//      .wdt ('x)
//    );
//    // response
//    rsp (
//      .rdt (dat),
//      .err (err)
//    );
//  endtask: read
//
//
//
//// write64
//// write32
// write16
// write8
// read64
// read32
// read16
// read8

endmodule: tcb_vip_man