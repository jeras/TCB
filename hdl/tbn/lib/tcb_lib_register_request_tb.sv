////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library register slice for request path testbench
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

module tcb_lib_register_request_tb
  import tcb_pkg::*;
  import tcb_vip_pkg::*;
#(
  // TCB widths
  int unsigned ADR = 32,       // address bus width
  int unsigned DAT = 32,       // data    bus width
  int unsigned SLW =       8,  // selection   width
  int unsigned BEW = DAT/SLW,  // byte enable width
  // response delay
  int unsigned DLY = 1,
  // bus hold granularity (byte granularity by default)
  int unsigned GRN = 1
);

  localparam DLY_MAN = DLY+1;
  localparam DLY_SUB = DLY;

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // response
  logic [DAT-1:0] rdt;  // read data
  logic           err;  // error response

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  tcb_if #(.ADR (ADR), .DAT (DAT), .DLY (DLY_MAN)) tcb_man       (.clk (clk), .rst (rst));
  tcb_if #(.ADR (ADR), .DAT (DAT), .DLY (DLY_SUB)) tcb_sub       (.clk (clk), .rst (rst));
  tcb_if #(.ADR (ADR), .DAT (DAT), .DLY (DLY_SUB)) tcb_mem [0:0] (.clk (clk), .rst (rst));

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
    man.write(32'h00000010, 64'h01234567, err);
    man.read (32'h00000010, rdt         , err);
    repeat (4) @(posedge clk);
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  tcb_vip_dev    #("MAN") man     (.tcb (tcb_man));  // manager
  tcb_vip_dev    #("MON") mon_man (.tcb (tcb_man));  // manager monitor
  tcb_vip_dev    #("MON") mon_sub (.tcb (tcb_sub));  // subordinate monitor
  tcb_vip_memory          mem     (.tcb (tcb_mem));  // subordinate

  // connect interfaces to interface array
  tcb_lib_passthrough pas [0:0] (.sub (tcb_sub), .man (tcb_mem));

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

  tcb_lib_register_request #(
    .GRN  (GRN)
  ) dut (
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

endmodule: tcb_lib_register_request_tb
