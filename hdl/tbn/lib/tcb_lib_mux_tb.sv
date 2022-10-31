////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) LIBrary MUltipleXer/ARBiter TestBench
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

module tcb_lib_mux_tb
  import tcb_vip_pkg::*;
#(
  // bus widths
  int unsigned AW = 32,     // address     width
  int unsigned DW = 32,     // data        width
  int unsigned SW =     8,  // selection   width
  int unsigned BW = DW/SW,  // byte enable width
  // response delay
  int unsigned DLY = 1,
  // interconnect parameters
  int unsigned PN = 2,      // port number
  localparam   PL = $clog2(PN)
);

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // response
  logic [DW-1:0] rdt;  // read data
  logic          err;  // error response

  // control
  logic [PL-1:0] sel;  // select

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  tcb_if #(.AW (AW), .DW (DW)) bus_man [PN-1:0] (.clk (clk), .rst (rst));
  tcb_if #(.AW (AW), .DW (DW)) bus_sub          (.clk (clk), .rst (rst));

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
        man.write(32'h01234567, 4'b1111, 64'h89ABCDEF, err);
        man.read (32'h76543210, 4'b1111, rdt         , err);
      end: req
      begin: rsp
        sub.rsp(32'hXXXXXXXX, 1'b0);
        sub.rsp(32'hFEDCBA98, 1'b0);
      end: rsp
    join
    repeat (8) @(posedge clk);
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// instances
////////////////////////////////////////////////////////////////////////////////

  // VIP managers
  tcb_vip_man #(
    // bus widths
    .AW   (AW),
    .DW   (DW),
    // response delay
    .DLY  (DLY)
  ) man [PN-1:0] (
    .bus  (bus_man)
  );

  // RTL arbiter DUT
  tcb_lib_pas #(
    // interconnect parameters
    .PN   (PN),
    // arbitration priority mode
//  .MD   (),
    // port priorities (lower number is higher priority)
    .PRI  ('{1, 0})
  ) mux (
    .sub  (bus_man),
    .sel  (sel)
  );

  // RTL multiplexer DUT
  tcb_lib_mux #(
    // bus widths
    .AW   (AW),
    .DW   (DW),
    // response delay
    .DLY  (DLY),
    // interconnect parameters
    .PN   (PN)
  ) mux (
    // control
    .sel  (sel),
    // TCB interfaces
    .sub  (bus_man),
    .man  (bus_sub)
  );

  // VIP subordinate
  tcb_vip_sub #(
    // bus widths
    .AW   (AW),
    .DW   (DW),
    // response delay
    .DLY  (DLY)
  ) sub (
    .bus  (bus_sub)
  );

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_lib_mux_tb