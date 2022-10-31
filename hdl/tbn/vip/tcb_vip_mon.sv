////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verifivation IP) MONitor
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

module tcb_vip_mon
  import tcb_vip_pkg::*;
(
  // TCB interface
  tcb_if.mon tcb
);

////////////////////////////////////////////////////////////////////////////////
// custom type and function definitions
////////////////////////////////////////////////////////////////////////////////

  // request structure
  typedef struct packed {
    // request
    logic              wen;  // write enable
    logic [tcb.AW-1:0] adr;  // address
    logic [tcb.BW-1:0] ben;  // byte enable
    logic [tcb.DW-1:0] wdt;  // write data
    // request optional
    logic              lck;  // arbitration lock
    logic              rpt;  // repeat access
  } tcb_req_t;

  // response structure  
  typedef struct packed {
    // response
    logic [tcb.DW-1:0] rdt;  // read data
    logic              err;  // error
  } tcb_rsp_t;

  // timing structure
  typedef struct packed {
    int unsigned       idl;  // idle
    int unsigned       bpr;  // backpressure
  } tcb_tmg_t;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // monitor delay buffer
  tcb_req_t req [0:tcb.DLY-1];  // request queue
  tcb_rsp_t rsp;                // response 
  tcb_tmg_t tmg [0:tcb.DLY-1];  // timing queue
  // monitor delay buffer pointers
  int unsigned wra;  // write address
  int unsigned rda;  // read  address

  // timing counters
  int unsigned cnt_idl;  // idle
  int unsigned cnt_bpr;  // backpressure

  // request
  always_ff @(posedge tcb.clk, posedge tcb.rst)
  if (tcb.rst) begin
    // clear monitor FIFO pointers
    wra <= 0;
    // timing initialize
    cnt_idl <= 0;
    cnt_bpr <= 0;
  end else begin
    // monitor delay buffer
    if (tcb.trn) begin
      wra <= (wra + 1) % tcb.DLY;
      // request
      req[wra] <= '{
        // request
        wen: tcb.wen,
        adr: tcb.adr,
        ben: tcb.ben,
        wdt: tcb.wdt,
        // request optional
        lck: tcb.lck,
        rpt: tcb.rpt
      };
      // timing
      tmg[wra] <= '{
        idl: cnt_idl,
        bpr: cnt_bpr
      };
    end
    // timing counters
    if (tcb.trn) begin
      // timing restart
      cnt_idl <= 0;
      cnt_bpr <= 0;
    end else begin
      // timing increments
      if (~tcb.vld) begin
        // increment idle counter
        cnt_idl <= cnt_idl + 1;
      end else begin
        // increment backpressure counter
        cnt_bpr <= cnt_bpr + 1;
      end
    end
  end

////////////////////////////////////////////////////////////////////////////////
// protocol check
////////////////////////////////////////////////////////////////////////////////

// TODO: on reads where byte enables bits are not active

////////////////////////////////////////////////////////////////////////////////
// logging
////////////////////////////////////////////////////////////////////////////////

  // response
  always_ff @(posedge tcb.clk, posedge tcb.rst)
  if (tcb.rst) begin
    // clear monitor FIFO pointers
    rda <= 0;
  end else begin
    if (tcb.rsp) begin
      rda <= (rda + 1) % tcb.DLY;
      // log printout
      $display("@%m: TCB log: %s: adr=0x%h ben=0b%b dat=0x%h txt=\"%4s\" err=%b",
        // request
        req[rda].wen ? "W" : "R",
        req[rda].adr,
        req[rda].ben,
        // data
                        req[rda].wen ? req[rda].wdt : tcb.rdt ,
        $sformatf("%s", req[rda].wen ? req[rda].wdt : tcb.rdt),
        // response error
        tcb.err
      );
    end
  end

////////////////////////////////////////////////////////////////////////////////
// statistics
////////////////////////////////////////////////////////////////////////////////

// TODO add delay counter, statistics

endmodule: tcb_vip_mon