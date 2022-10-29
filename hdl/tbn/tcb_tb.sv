////////////////////////////////////////////////////////////////////////////////
// R5P testbench for core module
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

module tcb_tb
  import tcb_pkg::*;
#(
  // bus widths
  int unsigned AW = 32,     // address   width
  int unsigned DW = 32,     // data      width
  int unsigned SW = 8,      // selection width
  int unsigned BW = DW/SW,  // byte ena. width
  // response delay
  int unsigned DLY = 1
);

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  logic [DW-1:0] rdt;  // read data
  logic          err;  // error response

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  tcb_if #(.AW (AW), .DW (DW)) bus (.clk (clk), .rst (rst));

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
      //           wen,  adr,     ben,          wdt,          rdt,  err, len
      man.write('h00, 4'b1111, 32'h01234567, err);
      man.read ('h00, 4'b1111, rdt         , err);
//        man.req('{1'b1, 'h00, 4'b1111, 32'h01234567,                     0});
//        sub.rsp('{                                   32'h89abcdef, 1'b0, 0});
//        man.req('{1'b1, 'h01, 4'b1111, 32'h76543210,                     1});
//        sub.rsp('{                                   32'hfedcba98, 1'b0, 1});
      end: req
      begin: rsp
        sub.rsp(32'h55xxxxxx, 1'b0);
        sub.rsp(32'h76543210, 1'b0);
//  //    man.rsp(                                            rdt,  err);
//  //    sub.req( wen,  adr,     ben,          wdt,                   );
      end: rsp
    join
    repeat (8) @(posedge clk);
    $finish();
  end

  tcb_man #(
    // bus widths
    .AW   (AW),
    .DW   (DW),
    // response delay
    .DLY  (DLY)
  ) man (
    .bus  (bus)
  );

  tcb_sub #(
    // bus widths
    .AW   (AW),
    .DW   (DW),
    // response delay
    .DLY  (DLY)
  ) sub (
    .bus  (bus)
  );

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_tb