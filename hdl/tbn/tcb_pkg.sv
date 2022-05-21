////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus package
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
///////////////////////////////////////////////////////////////////////////////

package tcb_pkg;

  localparam int unsigned AW = 32;    // address width
  localparam int unsigned DW = 32;    // data    width
  localparam int unsigned BW = DW/8;  // byte e. width

  typedef struct packed {
    logic          wen;  // write enable
    logic [AW-1:0] adr;  // address
    logic [BW-1:0] ben;  // byte enable
    logic [DW-1:0] wdt;  // write data
  } tcb_req_t;

  typedef struct packed {
    logic [DW-1:0] rdt;  // read data
    logic          err;  // error
  } tcb_rsp_t;

  // manager
  class tcb_man #(
    int unsigned AW = 32,    // address width
    int unsigned DW = 32,    // data    width
    int unsigned BW = DW/8   // byte e. width
  );

    tcb_req_t que_req [$];  // request  queue
    tcb_rsp_t que_rsp [$];  // response queue

    virtual tcb_if.man bus;

    // constructor
    function new(virtual tcb_if.man bus);
      this.bus = bus;
      // idle
      bus.vld <= 1'b0;
    endfunction

    // request
    task req (
      input  logic              wen,     // write enable
      input  logic [bus.AW-1:0] adr,     // address
      input  logic [bus.BW-1:0] ben,     // byte enable
      input  logic [bus.DW-1:0] wdt,     // write data
      input  int unsigned       dly = 0  // valid delay
    );
      repeat (dly)  @(posedge bus.clk);
      bus.vld <= 1'b1;
      bus.wen <= wen;
      bus.adr <= adr;
      bus.ben <= ben;
      bus.wdt <= wdt;
      while (~bus.trn)  @(posedge bus.clk);
      // remove valid
      bus.vld <= 1'b0;
      bus.wen <= 'x;
      bus.adr <= 'x;
      bus.ben <= 'x;
      bus.wdt <= 'x;
      $display("man.req done");
    endtask: req

    // response
    task rsp (
      input  logic [bus.DW-1:0] rdt,     // read data
      input  logic              err      // error
    );
      while (~bus.trn)  @(posedge bus.clk);
      // read data
      bus.rdt <= rdt;
      bus.err <= err;
      $display("man.rsp done");
    endtask: rsp

  endclass: tcb_man

  // subordinate
  class tcb_sub;

    virtual tcb_if.sub bus;

    // constructor
    function new(virtual tcb_if.sub bus);
      this.bus <= bus;
      // idle
      bus.rdy <= 1'b0;
    endfunction

    // response
    task rsp (
      input  logic [bus.DW-1:0] rdt,     // read data
      input  logic              err,     // error
      input  int unsigned       dly = 0  // valid delay
    );
      repeat (dly)  @(posedge bus.clk);
      bus.rdy <= 1'b1;
      while (~bus.trn)  @(posedge bus.clk);
      // read data
      bus.rdy <= 1'b0;
      bus.rdt <= rdt;
      bus.err <= err;
      $display("sub.rsp done");
    endtask: rsp

  endclass: tcb_sub

endpackage: tcb_pkg