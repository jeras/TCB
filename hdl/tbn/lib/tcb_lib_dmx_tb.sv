////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) LIBrary DeMultipleXer/DECoder TestBench
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

module tcb_lib_dmx_tb
  import tcb_vip_pkg::*;
#(
  // TCB widths
  int unsigned ABW = 32,       // address bus width
  int unsigned DBW = 32,       // data    bus width
  int unsigned SLW =       8,  // selection   width
  int unsigned BEW = DBW/SLW,  // byte enable width
  // response delay
  int unsigned DLY = 1,
  // interconnect parameters
  int unsigned PN = 3,      // port number
  int unsigned PL = $clog2(PN),
  // decoder address and mask array
  parameter  logic [ABW-1:0] DAM [PN-1:0] = '{PN{ABW'('x)}}
);

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // response
  logic [DBW-1:0] rdt;  // read data
  logic           err;  // error response

  // control
  logic  [PL-1:0] sel;  // select

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  tcb_if #(.ABW (ABW), .DBW (DBW)) tcb_man           (.clk (clk), .rst (rst));
  tcb_if #(.ABW (ABW), .DBW (DBW)) tcb_sub  [PN-1:0] (.clk (clk), .rst (rst));

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  initial          clk = 1'b1;
  always #(20ns/2) clk = ~clk;

  // test sequence
  initial
  begin
    // reset sequence
    rst = 1'b1;
    repeat (2) @(posedge clk);
    rst = 1'b0;
    repeat (1) @(posedge clk);
    #1;
    fork
      begin: req
        man.write(32'h00000000, 4'b1111, 32'h03020100, err);
        man.write(32'h00000004, 4'b1111, 32'h13121110, err);
        man.write(32'h0000000C, 4'b1111, 32'h23222120, err);
        man.read (32'h00000000, 4'b1111, rdt, err);
        man.read (32'h00000004, 4'b1111, rdt, err);
        man.read (32'h0000000C, 4'b1111, rdt, err);
      end: req
      begin: rsp
        fork
          begin  sub[0].rsp(32'hXXXXXXXX, 1'b0);  end
          begin  sub[1].rsp(32'hXXXXXXXX, 1'b0);  end
          begin  sub[2].rsp(32'hXXXXXXXX, 1'b0);  end
        join
        fork
          begin  sub[0].rsp(32'h03020100, 1'b0);  end
          begin  sub[1].rsp(32'h13121110, 1'b0);  end
          begin  sub[2].rsp(32'h23222120, 1'b0);  end
        join
      end: rsp
    join
    repeat (8) @(posedge clk);
    $finish();
  end

  // timeout
  initial
  begin
    repeat (20) @(posedge clk);
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  // manager
  tcb_vip_man man              (.tcb (tcb_man));

  // manager monitor
  tcb_vip_mon mon_man          (.tcb (tcb_man));

  // subordinate monitor
  tcb_vip_mon mon_sub [PN-1:0] (.tcb (tcb_sub));

  // subordinate
  tcb_vip_sub sub     [PN-1:0] (.tcb (tcb_sub));

////////////////////////////////////////////////////////////////////////////////
// DUT instances
////////////////////////////////////////////////////////////////////////////////

  // RTL decoder DUT
  tcb_lib_dec #(
    // arbitration priority mode
//  .MD   (),
    // interconnect parameters
    .PN   (PN),
    // decoder address and mask array
    .DAM  (DAM)
  ) arb (
    .tcb  (tcb_man),
    .sel  (sel)
  );

  // RTL demultiplexer DUT
  tcb_lib_dmx #(
    // interconnect parameters
    .PN   (PN)
  ) mux (
    // control
    .sel  (sel),
    // TCB interfaces
    .sub  (tcb_man),
    .man  (tcb_sub)
  );

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_lib_dmx_tb