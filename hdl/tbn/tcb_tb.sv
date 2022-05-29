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
///////////////////////////////////////////////////////////////////////////////

module tcb_tb
  import tcb_pkg::*;
#(
  // bus widths
  int unsigned AW = 32,    // address width
  int unsigned DW = 32,    // data    width
  int unsigned BW = DW/8,  // byte e. width
  // response delay
  int unsigned DLY = 1
)(
  // system signals
  input  logic clk,  // clock
  input  logic rst   // reset
);

  // system signals
  logic clk = 1'b1;  // clock
  logic rst = 1'b1;  // reset

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  tcb_if #(.AW (AW), .DW (DW)) bus (.clk (clk), .rst (rst));

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  always #(20ns/2) clk = ~clk;

  // reset
  initial
  begin
    // manager/subordinate
//    tcb_man man = new(bus.man);
//    tcb_sub sub = new(bus.sub);
    // reset sequence
    repeat (4) @(posedge clk);
    rst <= 1'b0;
    repeat (1) @(posedge clk);
    fork
      //               wen,  adr,     ben,          wdt,          rdt,  err, len
        man.req_trn('{1'b1, 'h00, 4'b1111, 32'h01234567,                     1});
        sub.rsp_trn('{                                   32'h89abcdef, 1'b0, 1});
  //    man.rsp_trn(                                            rdt,  err);
  //    sub.req_trn( wen,  adr,     ben,          wdt,                   );
    join
    repeat (8) @(posedge clk);
    $finish();
  end

  tcb_man #(
    .DLY  (DLY)
  ) man (
    .bus  (bus)
  );

  tcb_sub #(
    .DLY  (DLY)
  ) sub (
    .bus  (bus)
  );

/*
////////////////////////////////////////////////////////////////////////////////
// timeout
////////////////////////////////////////////////////////////////////////////////

// clock period counter
int unsigned cnt;
bit timeout = 1'b0;

// time counter
always_ff @(posedge clk, posedge rst)
if (rst) begin
  cnt <= 0;
end else begin
  cnt <= cnt+1;
end

// timeout
//always @(posedge clk)
//if (cnt > 5000)  timeout <= 1'b1;

////////////////////////////////////////////////////////////////////////////////
// waveforms
////////////////////////////////////////////////////////////////////////////////

//initial begin
//  $dumpfile("tcb_tb.vcd");
//  $dumpvars(0, tcb_tb);
//end
*/
endmodule: tcb_tb
