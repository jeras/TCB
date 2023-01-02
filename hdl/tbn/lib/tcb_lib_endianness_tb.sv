////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library endianness converter testbench
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

module tcb_lib_endianness_tb
  import tcb_vip_pkg::*;
#(
  // TCB widths
  int unsigned ABW = 64,       // address bus width
  int unsigned DBW = 64,       // data    bus width
  int unsigned SLW =       8,  // selection   width
  int unsigned BEW = DBW/SLW,  // byte enable width
  // response delay
  int unsigned DLY = 1
);

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // response
  logic [DBW-1:0] rdt;  // read data
  logic           err;  // error response

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  tcb_if #(.ABW (ABW), .DBW (DBW), .DLY (DLY)) tcb_man (.clk (clk), .rst (rst));
  tcb_if #(.ABW (ABW), .DBW (DBW), .DLY (DLY)) tcb_sub (.clk (clk), .rst (rst));

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
        man.write(64'h0123456789ABCDEF, 8'b11111111, 64'h0123456789ABCDEF, err);
        man.read (64'hFEDCBA9876543210, 8'b11111111, rdt                 , err);
      end: req
      begin: rsp
        sub.rsp(64'hXXXXXXXXXXXXXXXX, 1'b0);
        sub.rsp(64'hFEDCBA9876543210, 1'b0);
      end: rsp
    join
    repeat (8) @(posedge clk);
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  tcb_vip_dev #("MAN") man     (.tcb (tcb_man));  // manager
  tcb_vip_dev #("MON") mon_man (.tcb (tcb_man));  // manager monitor
  tcb_vip_dev #("MON") mon_sub (.tcb (tcb_sub));  // subordinate monitor
  tcb_vip_dev #("SUB") sub     (.tcb (tcb_sub));  // subordinate

////////////////////////////////////////////////////////////////////////////////
// DUT instances
////////////////////////////////////////////////////////////////////////////////

  // RTL passthrough
  tcb_lib_reg dut (
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

endmodule: tcb_lib_endianness_tb