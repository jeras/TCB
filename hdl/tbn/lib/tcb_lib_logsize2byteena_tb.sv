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
  // handshake parameter
  parameter  int unsigned      HSK_DLY = TCB_HSK_DEF      // response delay
//  // bus parameters
//  parameter  tcb_bus_channel_t BUS_CHN = TCB_BUS_DEF.CHN,  // channel configuration
//  parameter  tcb_bus_mode_t    BUS_MOD = TCB_BUS_DEF.MOD,  // manager     data position mode
//  // data packing parameters for manager/subordinate
//  parameter  int unsigned      BUS_ALN = TCB_BUS_DEF.ALN,  // TODO
//  parameter  int unsigned      BUS_MIN = TCB_BUS_DEF.MIN,  // TODO
//  parameter  int unsigned      BUS_OFF = TCB_BUS_DEF.OFF,  // TODO
//  parameter  tcb_pck_order_t   PCK_ORD = TCB_BUS_DEF.ORD   // manager     byte order
);

  // physical interface parameter default
  localparam tcb_bus_t TCB_BUS_SIZ = '{
    FRM: TCB_FRM_ENABLED,
    CHN: TCB_CHN_HALF_DUPLEX,
    PRF: TCB_PRF_ENABLED,
    NXT: TCB_NXT_ENABLED,
    MOD: TCB_MOD_LOG_SIZE,
    NDN: TCB_NDN_BI_NDN
  };

  // physical interface parameter default
  localparam tcb_bus_t TCB_BUS_BEN = '{
    FRM: TCB_FRM_ENABLED,
    CHN: TCB_CHN_HALF_DUPLEX,
    PRF: TCB_PRF_ENABLED,
    NXT: TCB_NXT_ENABLED,
    MOD: TCB_MOD_BYTE_ENA,
    NDN: TCB_NDN_BI_NDN
  };

  // physical interface parameter default
  localparam tcb_pck_t TCB_PCK = '{
    ALN: 2,
    MIN: 0,
    OFF: 0,
    ORD: TCB_ORD_DESCENDING
  };

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals (initialized)
  logic clk = 1'b1;  // clock
  logic rst = 1'b1;  // reset

  // TCB interfaces
  tcb_if #(HSK_DLY, tcb_bus_t, TCB_BUS_SIZ, tcb_pck_t, TCB_PCK, tcb_req_t, tcb_rsp_t) tcb_man       (.clk (clk), .rst (rst));
  tcb_if #(HSK_DLY, tcb_bus_t, TCB_BUS_BEN, tcb_pck_t, TCB_PCK, tcb_req_t, tcb_rsp_t) tcb_sub       (.clk (clk), .rst (rst));
  tcb_if #(HSK_DLY, tcb_bus_t, TCB_BUS_BEN, tcb_pck_t, TCB_PCK, tcb_req_t, tcb_rsp_t) tcb_mem [0:0] (.clk (clk), .rst (rst));

  // parameterized class specialization
  typedef tcb_vip_blocking_c #(HSK_DLY, tcb_bus_t, TCB_BUS_SIZ, tcb_pck_t, TCB_PCK, tcb_req_t, tcb_rsp_t) tcb_vip_siz_s;
  typedef tcb_vip_blocking_c #(HSK_DLY, tcb_bus_t, TCB_BUS_BEN, tcb_pck_t, TCB_PCK, tcb_req_t, tcb_rsp_t) tcb_vip_ben_s;

  // TCB class objects
  tcb_vip_siz_s obj_man = new(tcb_man, "MAN");
  tcb_vip_ben_s obj_sub = new(tcb_sub, "MON");

  // transfer reference/monitor array
  tcb_vip_ben_s::transfer_queue_t tst_ref;
  tcb_vip_ben_s::transfer_queue_t tst_mon;

  // empty array
  logic [8-1:0] nul [];

  // response
  logic [tcb_man.BUS_BEN-1:0][8-1:0] rdt;  // read data
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
      begin: fork_man_write
        obj_man.write8 (32'h00000010,        8'h10, sts);
        obj_man.write8 (32'h00000011,      8'h32  , sts);
        obj_man.write8 (32'h00000012,    8'h54    , sts);
        obj_man.write8 (32'h00000013,  8'h76      , sts);
        obj_man.write16(32'h00000020,     16'h3210, sts);
        obj_man.write16(32'h00000022, 16'h7654    , sts);
        obj_man.write32(32'h00000030, 32'h76543210, sts);
      end: fork_man_write
      // subordinate (monitor)
      begin: fork_mon_write
        obj_sub.transfer_monitor(tst_mon);
      end: fork_mon_write
    join_any
    // disable transfer monitor
    @(posedge clk);
    disable fork;
    // reference transfer queue
    sts = '0;
    //                                                   ndn       , wen , adr         , wdt                           ,        rdt
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000010, '{8'h10                     }}, rsp: '{nul, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000011, '{       8'h32              }}, rsp: '{nul, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000012, '{              8'h54       }}, rsp: '{nul, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000013, '{                     8'h76}}, rsp: '{nul, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000020, '{8'h10, 8'h32              }}, rsp: '{nul, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000022, '{              8'h54, 8'h76}}, rsp: '{nul, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000030, '{8'h10, 8'h32, 8'h54, 8'h76}}, rsp: '{nul, sts}, default: 'x})};
    // compare transfers from monitor to reference
    foreach(tst_ref[i]) begin
      assert (tst_mon[i].req ==? tst_ref[i].req) else $error("\ntst_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_mon[i].req, i, tst_ref[i].req);
      assert (tst_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_mon[i].rsp, i, tst_ref[i].rsp);
    end

    // read sequence
    $display("read sequence");
    testname = "read";
    fork
      // manager (blocking API)
      begin: fork_man_read
        obj_man.read8  (32'h00000010, rdt[1-1:0], sts);
        obj_man.read8  (32'h00000011, rdt[1-1:0], sts);
        obj_man.read8  (32'h00000012, rdt[1-1:0], sts);
        obj_man.read8  (32'h00000013, rdt[1-1:0], sts);
        obj_man.read16 (32'h00000020, rdt[2-1:0], sts);
        obj_man.read16 (32'h00000022, rdt[2-1:0], sts);
        obj_man.read32 (32'h00000030, rdt[4-1:0], sts);
      end: fork_man_read
      // subordinate (monitor)
      begin: fork_mon_read
        obj_sub.transfer_monitor(tst_mon);
      end: fork_mon_read
    join_any
    // disable transfer monitor
    @(posedge clk);
    disable fork;
    // reference transfer queue
    sts = '0;
    //                                                   ndn       , wen , adr         , wdt ,        rdt
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b0, 32'h00000010, nul}, rsp: '{'{8'h10                     }, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b0, 32'h00000011, nul}, rsp: '{'{       8'h32              }, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b0, 32'h00000012, nul}, rsp: '{'{              8'h54       }, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b0, 32'h00000013, nul}, rsp: '{'{                     8'h76}, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b0, 32'h00000020, nul}, rsp: '{'{8'h10, 8'h32              }, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b0, 32'h00000022, nul}, rsp: '{'{              8'h54, 8'h76}, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b0, 32'h00000030, nul}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}, default: 'x})};
    foreach(tst_ref[i]) begin
      assert (tst_mon[i].req ==? tst_ref[i].req) else $error("\ntst_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_mon[i].req, i, tst_ref[i].req);
      assert (tst_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_mon[i].rsp, i, tst_ref[i].rsp);
    end

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

/*
    // misaligned write sequence
    $display("misaligned write sequence");
    testname = "misaligned write";
    // clear memory
    mem.mem = '{default: 'x};
    // test sequence
    fork
      // manager (blocking API)
      begin: fork_man_misaligned_write
        obj_man.write16(32'h00000011, 16'h3210    , sts);
        obj_man.write16(32'h00000023, 16'h7654    , sts);
        obj_man.write32(32'h00000031, 32'h76543210, sts);
        obj_man.write32(32'h00000042, 32'h76543210, sts);
        obj_man.write32(32'h00000053, 32'h76543210, sts);
      end: fork_man_misaligned_write
      // subordinate (monitor)
      begin: fork_mon_misaligned_write
        obj_sub.transfer_monitor(tst_mon);
      end: fork_mon_misaligned_write
    join_any
    // disable transfer monitor
    @(posedge clk);
    disable fork;
    // reference transfer queue
    sts = '0;
    //                                                   ndn       , wen , adr         , wdt                           ,        rdt
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000011, '{8'h10, 8'h32              }}, rsp: '{nul, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000023, '{8'h54, 8'h76              }}, rsp: '{nul, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000031, '{8'h10, 8'h32, 8'h54, 8'h76}}, rsp: '{nul, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000042, '{8'h10, 8'h32, 8'h54, 8'h76}}, rsp: '{nul, sts}, default: 'x})};
    tst_ref = {tst_ref, obj_sub.set_transaction('{req: '{TCB_LITTLE, 1'b1, 32'h00000053, '{8'h10, 8'h32, 8'h54, 8'h76}}, rsp: '{nul, sts}, default: 'x})};
    // compare transfers from monitor to reference
    foreach(tst_ref[i]) begin
      assert (tst_mon[i].req ==? tst_ref[i].req) else $error("\ntst_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_mon[i].req, i, tst_ref[i].req);
      assert (tst_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_mon[i].rsp, i, tst_ref[i].rsp);
    end
*/
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
