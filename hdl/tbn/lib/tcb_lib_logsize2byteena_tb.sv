////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library logsize2byteena testbench
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

module tcb_lib_logsize2byteena_tb
  import tcb_pkg::*;
  import tcb_vip_blocking_pkg::*;
#(
  // protocol
  parameter  int unsigned      DLY     = TCB_DLY_DEF,      // response delay
  // data packing parameters for manager/subordinate
  parameter  int unsigned      PHY_ALN = TCB_PHY_DEF.ALN,  // TODO
  parameter  int unsigned      PHY_MIN = TCB_PHY_DEF.MIN,  // TODO
  parameter  int unsigned      PHY_OFF = TCB_PHY_DEF.OFF,  // TODO
  parameter  tcb_phy_mode_t    PHY_MOD = TCB_PHY_DEF.MOD,  // manager     data position mode
  parameter  tcb_phy_order_t   PHY_ORD = TCB_PHY_DEF.ORD,  // manager     byte order
  // channel configuration
  parameter  tcb_phy_channel_t PHY_CHN = TCB_PHY_DEF.CHN  // channel configuration
);

  localparam tcb_phy_t TCB_PHY_SIZ = '{
    // data packing parameters
    ALN: 2,
    MIN: 0,
    OFF: 0,
    MOD: TCB_LOG_SIZE,
    ORD: PHY_ORD,
    // channel configuration
    CHN: PHY_CHN
  };

  localparam tcb_phy_t TCB_PHY_BEN = '{
    // data packing parameters
    ALN: 2,
    MIN: 0,
    OFF: 0,
    MOD: TCB_BYTE_ENA,
    ORD: PHY_ORD,
    // channel configuration
    CHN: PHY_CHN
  };

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals (initialized)
  logic clk = 1'b1;  // clock
  logic rst = 1'b1;  // reset

  // TCB interfaces
  tcb_if #(DLY, tcb_phy_t, TCB_PHY_SIZ, tcb_req_t, tcb_rsp_t) tcb_man       (.clk (clk), .rst (rst));
  tcb_if #(DLY, tcb_phy_t, TCB_PHY_BEN, tcb_req_t, tcb_rsp_t) tcb_sub       (.clk (clk), .rst (rst));
  tcb_if #(DLY, tcb_phy_t, TCB_PHY_BEN, tcb_req_t, tcb_rsp_t) tcb_mem [0:0] (.clk (clk), .rst (rst));

  // parameterized class specialization
  typedef tcb_vip_blocking_c #(DLY, tcb_phy_t, TCB_PHY_SIZ, tcb_req_t, tcb_rsp_t) tcb_vip_siz_s;
  typedef tcb_vip_blocking_c #(DLY, tcb_phy_t, TCB_PHY_BEN, tcb_req_t, tcb_rsp_t) tcb_vip_ben_s;

  // TCB class objects
  tcb_vip_siz_s obj_man = new(tcb_man, "MAN");
  tcb_vip_ben_s obj_sub = new(tcb_sub, "MON");

  // transfer reference/monitor array
  tcb_vip_ben_s::transfer_queue_t tst_tmp;
  tcb_vip_ben_s::transfer_queue_t tst_ref;
  tcb_vip_ben_s::transfer_queue_t tst_mon;

////////////////////////////////////////////////////////////////////////////////
// data checking
////////////////////////////////////////////////////////////////////////////////

  // response
  logic [tcb_man.PHY_BEN-1:0][8-1:0] rdt;  // read data
  tcb_rsp_sts_t                      sts;  // status response

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  string testname = "none";

  // clock
  always #(20ns/2) clk = ~clk;

  // test sequence
  initial
  begin: test
    // reset sequence
    repeat (2) @(posedge clk);
    rst <= 1'b0;
    repeat (1) @(posedge clk);

    // write sequence
    $display("write sequence");
    testname = "write";
    fork
      // manager (blocking API)
      begin: fork_man
        obj_man.write8 (32'h00000010,        8'h10, sts);
        obj_man.write8 (32'h00000011,      8'h32  , sts);
        obj_man.write8 (32'h00000012,    8'h54    , sts);
        obj_man.write8 (32'h00000013,  8'h76      , sts);
        obj_man.write16(32'h00000020,     16'h3210, sts);
        obj_man.write16(32'h00000022, 16'h7654    , sts);
        obj_man.write32(32'h00000030, 32'h76543210, sts);            
      end: fork_man
      // subordinate (monitor)
      begin: fork_mon
        obj_sub.transfer_monitor(tst_mon);
      end: fork_mon
    join_any
    // disable transfer monitor
    @(posedge clk);
    disable fork;
    // reference transfer queue
    sts = '0;
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000010, '{8'h10}}, rsp: '{'{default: 'x}, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000011, '{8'h32}}, rsp: '{'{default: 'x}, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000012, '{8'h54}}, rsp: '{'{default: 'x}, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000013, '{8'h76}}, rsp: '{'{default: 'x}, sts}, default: 'x})};

    // compare transfers from monitor to reference
    foreach(tst_mon[i]) $display("DEBUG: tst_ref[%0d] = %p", i, tst_ref[i]);
    foreach(tst_mon[i]) $display("DEBUG: tst_mon[%0d] = %p", i, tst_mon[i]);
    
    // read sequence
    $display("read sequence");
    testname = "read";
    obj_man.read8  (32'h00000010, rdt[1-1:0]  , sts);
    obj_man.read8  (32'h00000011, rdt[1-1:0]  , sts);
    obj_man.read8  (32'h00000012, rdt[1-1:0]  , sts);
    obj_man.read8  (32'h00000013, rdt[1-1:0]  , sts);
    obj_man.read16 (32'h00000020, rdt[2-1:0]  , sts);
    obj_man.read16 (32'h00000022, rdt[2-1:0]  , sts);
    obj_man.read32 (32'h00000030, rdt[4-1:0]  , sts);

    // check sequence
    $display("check sequence");
    testname = "check";
    obj_man.check8 (32'h00000010,        8'h10, 1'b0);
    obj_man.check8 (32'h00000011,      8'h32  , 1'b0);
    obj_man.check8 (32'h00000012,    8'h54    , 1'b0);
    obj_man.check8 (32'h00000013,  8'h76      , 1'b0);
    obj_man.check32(32'h00000010, 32'h76543210, 1'b0);
    obj_man.check16(32'h00000020,     16'h3210, 1'b0);
    obj_man.check16(32'h00000022, 16'h7654    , 1'b0);
    obj_man.check32(32'h00000020, 32'h76543210, 1'b0);
    obj_man.check32(32'h00000030, 32'h76543210, 1'b0);
    // end of test
    repeat (4) @(posedge clk);
    $finish();
  end: test

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  // connect singular interface to interface array
  tcb_lib_passthrough pas [0:0] (
    .sub (tcb_sub),
    .man (tcb_mem)
  );

  // memory model subordinate
  tcb_vip_memory #(
    .SIZ (2**8)
  ) mem (
    .tcb (tcb_mem)
  );

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

  tcb_lib_logsize2byteena dut (
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

endmodule: tcb_lib_logsize2byteena_tb
