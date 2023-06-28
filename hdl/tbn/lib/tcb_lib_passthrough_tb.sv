////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library passthrough testbench
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

module tcb_lib_passthrough_tb
  import tcb_pkg::*;
  import tcb_vip_pkg::*;
#(
  // TCB widths
  int unsigned ABW = 32,
  int unsigned DBW = 32,
  // response delay
  int unsigned DLY = 1
);

  // TODO: parameter propagation through virtual interfaces in classes
  // is not working well thus this workaround

  // physical interface parameter
  localparam tcb_par_phy_t PHY1 = '{
    // signal bus widths
    SLW: TCB_PAR_PHY_DEF.SLW,
    ABW: ABW,
    DBW: DBW,
    // TCB parameters
    DLY: DLY,
    // mode/alignment/order parameters
    MOD: TCB_PAR_PHY_DEF.MOD,
    SIZ: TCB_PAR_PHY_DEF.SIZ,
    ORD: TCB_PAR_PHY_DEF.ORD,
    LGN: TCB_PAR_PHY_DEF.LGN
  };

  localparam tcb_par_phy_t PHY = TCB_PAR_PHY_DEF;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals
  logic clk;  // clock
  logic rst;  // reset
/*
  // TCB interfaces
  tcb_if #(.PHY (PHY)) tcb_man (.clk (clk), .rst (rst));
  tcb_if #(.PHY (PHY)) tcb_sub (.clk (clk), .rst (rst));
*/
  // TODO: the above code should be used instead
  // TCB interfaces
  tcb_if tcb_man (.clk (clk), .rst (rst));
  tcb_if tcb_sub (.clk (clk), .rst (rst));

  // parameterized class specialization
  typedef tcb_transfer_c #(.PHY (PHY)) tcb_s;

  // TCB class objects
  tcb_s obj_man;
  tcb_s obj_sub;

////////////////////////////////////////////////////////////////////////////////
// data checking
////////////////////////////////////////////////////////////////////////////////

  // response
  logic [PHY.DBW-1:0] rdt;  // read data
  tcb_rsp_sts_def_t   sts;  // status response

  logic [ 8-1:0] rdt8 ;  //  8-bit read data
  logic [16-1:0] rdt16;  // 16-bit read data
  logic [32-1:0] rdt32;  // 32-bit read data

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  initial          clk = 1'b1;
  always #(20ns/2) clk = ~clk;

  // test sequence
  initial
  begin
    // connect virtual interfaces
    obj_man = new("MAN", tcb_man);
    obj_sub = new("SUB", tcb_sub);
    // reset sequence
    rst = 1'b1;
    repeat (2) @(posedge clk);
    rst = 1'b0;
    repeat (1) @(posedge clk);
    fork
      begin: req
        obj_man.write32(32'h01234567, 32'h76543210, sts);
        obj_man.read32 (32'h89ABCDEF, rdt32       , sts);
      end: req
      begin: rsp
//        obj_sub.rsp(32'hXXXXXXXX, '0);
//        obj_sub.rsp(32'hFEDCBA98, '0);
      end: rsp
    join
    repeat (8) @(posedge clk);
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

  tcb_lib_passthrough dut (
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

endmodule: tcb_lib_passthrough_tb
