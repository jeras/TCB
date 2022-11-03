////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verifivation IP) manager/monitor/subordinate TestBench
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

module tcb_vip_tb
  import tcb_vip_pkg::*;
#(
  // TCB widths
  int unsigned ABW = 32,       // address bus width
  int unsigned DBW = 32,       // data    bus width
  int unsigned SLW =       8,  // selection   width
  int unsigned BEW = DBW/SLW,  // byte enable width
  // response delay
  int unsigned DLY = 2
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

  tcb_if #(.ABW (ABW), .DBW (DBW), .DLY (DLY)) tcb (.clk (clk), .rst (rst));

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
    #1;
    rst = 1'b0;
    repeat (1) @(posedge clk);
    fork
      begin: req
        //         adr,     ben,          wdt, err, len
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
    repeat (4) @(posedge clk);
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  // manager
  tcb_vip_man man (.tcb (tcb));

  // monitor
  tcb_vip_mon mon (.tcb (tcb));

  // subordinate
  tcb_vip_sub sub (.tcb (tcb));

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_vip_tb