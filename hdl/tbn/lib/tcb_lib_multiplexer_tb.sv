////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library multiplexer/arbiter testbench
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

module tcb_lib_multiplexer_tb
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
  // port priorities (lower number is higher priority)
  int unsigned PRI [PN-1:0] = '{2, 1, 0}
);

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // response
  //logic [DBW-1:0] rdt [PN-1:0];  // read data
  //logic           err [PN-1:0];  // error response
  logic [DBW-1:0] rdt;  // read data
  logic           err;  // error response

  // control
  logic  [PL-1:0] sel;  // select

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  tcb_if #(.ABW (ABW), .DBW (DBW)) tcb_man  [PN-1:0] (.clk (clk), .rst (rst));
  tcb_if #(.ABW (ABW), .DBW (DBW)) tcb_sub           (.clk (clk), .rst (rst));

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
//        for (int unsigned i=0; i<PN; i++) begin
//          man[i].write(32'h01234567, 4'b1111, 32'h89ABCDEF, err);
//          man[i].read (32'h76543210, 4'b1111, rdt         , err);
//        end
          // TODO: check why I could not drive an array element
          fork
//            begin  man[0].write(32'h00000000, 4'b1111, 32'h03020100, err[0]);  end
//            begin  man[1].write(32'h00000004, 4'b1111, 32'h13121110, err[1]);  end
//            begin  man[2].write(32'h0000000C, 4'b1111, 32'h23222120, err[2]);  end
            begin  man[0].write(32'h00000000, 4'b1111, 32'h03020100, err);  end
            begin  man[1].write(32'h00000004, 4'b1111, 32'h13121110, err);  end
            begin  man[2].write(32'h0000000C, 4'b1111, 32'h23222120, err);  end
          join
          fork
//            begin  man[0].read (32'h00000000, 4'b1111, rdt[0]      , err[0]);  end
//            begin  man[1].read (32'h00000004, 4'b1111, rdt[1]      , err[1]);  end
//            begin  man[2].read (32'h0000000C, 4'b1111, rdt[2]      , err[2]);  end
            begin  man[0].read (32'h00000000, 4'b1111, rdt, err);  end
            begin  man[1].read (32'h00000004, 4'b1111, rdt, err);  end
            begin  man[2].read (32'h0000000C, 4'b1111, rdt, err);  end
          join
      end: req
      begin: rsp
        sub.rsp(32'hXXXXXXXX, 1'b0);
        sub.rsp(32'hXXXXXXXX, 1'b0);
        sub.rsp(32'hXXXXXXXX, 1'b0);
        sub.rsp(32'h03020100, 1'b0);
        sub.rsp(32'h13121110, 1'b0);
        sub.rsp(32'h23222120, 1'b0);
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
// VIP component instances
////////////////////////////////////////////////////////////////////////////////

  tcb_vip_dev #("MAN") man     [PN-1:0] (.tcb (tcb_man));  // manager
  tcb_vip_dev #("MON") mon_man [PN-1:0] (.tcb (tcb_man));  // manager monitor
  tcb_vip_dev #("MON") mon_sub          (.tcb (tcb_sub));  // subordinate monitor
  tcb_vip_dev #("SUB") sub              (.tcb (tcb_sub));  // subordinate

////////////////////////////////////////////////////////////////////////////////
// DUT instances
////////////////////////////////////////////////////////////////////////////////

  // RTL arbiter DUT
  tcb_lib_arbiter #(
    // arbitration priority mode
//  .MD   (),
    // interconnect parameters
    .PN   (PN),
    // port priorities (lower number is higher priority)
    .PRI  (PRI)
  ) arb (
    .tcb  (tcb_man),
    .sel  (sel)
  );

  // RTL multiplexer DUT
  tcb_lib_multiplexer #(
    // interconnect parameters
    .PN   (PN)
  ) dut (
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

endmodule: tcb_lib_multiplexer_tb