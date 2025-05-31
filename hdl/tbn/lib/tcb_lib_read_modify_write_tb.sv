////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library read_modify_write testbench
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

module tcb_lib_read_modify_write_tb
  import tcb_pkg::*;
  import tcb_vip_blocking_pkg::*;
#(
  // handshake parameter
  parameter  int unsigned      DLY = TCB_HSK_DEF.DLY      // response delay
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  // handshake parameter
  localparam tcb_hsk_t HSK = TCB_HSK_DEF;

  // bus parameter
  localparam tcb_bus_t BUS_MAN = '{
    ADR: TCB_BUS_DEF.ADR,
    DAT: TCB_BUS_DEF.DAT,
    FRM: TCB_BUS_DEF.FRM,
    CHN: TCB_CHN_FULL_DUPLEX,
    AMO: TCB_AMO_ENABLED,
    PRF: TCB_PRF_DISABLED,
    NXT: TCB_NXT_DISABLED,
    MOD: TCB_MOD_LOG_SIZE,
    ORD: TCB_ORD_DESCENDING,
    NDN: TCB_NDN_BI_NDN
  };

  // bus parameter
  localparam tcb_bus_t BUS_SUB = '{
    ADR: TCB_BUS_DEF.ADR,
    DAT: TCB_BUS_DEF.DAT,
    FRM: TCB_BUS_DEF.FRM,
    CHN: TCB_CHN_FULL_DUPLEX,
    AMO: TCB_AMO_DISABLED,
    PRF: TCB_PRF_DISABLED,
    NXT: TCB_NXT_DISABLED,
    MOD: TCB_MOD_BYTE_ENA,
    ORD: TCB_ORD_DESCENDING,
    NDN: TCB_NDN_BI_NDN
  };

  // physical interface parameter default
  localparam tcb_pma_t PMA = '{
    MIN: 0,
    OFF: 0,
    ALN: 0,
    BND: 0
  };

  localparam tcb_vip_t VIP = '{
    DRV: 1'b1
  };

//  typedef tcb_c #(HSK, BUS_SIZ, PMA)::req_t req_t;
//  typedef tcb_c #(HSK, BUS_SIZ, PMA)::rsp_t rsp_t;

  // local request/response types are copies of packaged defaults
  typedef tcb_req_t req_t;
  typedef tcb_rsp_t rsp_t;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals (initialized)
  logic clk = 1'b1;  // clock
  logic rst = 1'b1;  // reset

  string testname = "none";

  // TCB interfaces
  tcb_if #(tcb_hsk_t, HSK, tcb_bus_t, BUS_MAN, tcb_pma_t, PMA, req_t, rsp_t                ) tcb_man       (.clk (clk), .rst (rst));
  tcb_if #(tcb_hsk_t, HSK, tcb_bus_t, BUS_SUB, tcb_pma_t, PMA, req_t, rsp_t                ) tcb_sub       (.clk (clk), .rst (rst));

  // parameterized class specialization (blocking API)
  typedef tcb_vip_blocking_c #(tcb_hsk_t, HSK, tcb_bus_t, BUS_MAN, tcb_pma_t, PMA, req_t, rsp_t) tcb_vip_siz_s;
  typedef tcb_vip_blocking_c #(tcb_hsk_t, HSK, tcb_bus_t, BUS_SUB, tcb_pma_t, PMA, req_t, rsp_t) tcb_vip_ben_s;

  // TCB class objects
  tcb_vip_siz_s obj_man = new(tcb_man, "MAN");
  tcb_vip_ben_s obj_sub = new(tcb_sub, "MON");

  // transfer reference/monitor array
  tcb_vip_ben_s::transfer_queue_t tst_ref;
  tcb_vip_ben_s::transfer_queue_t tst_mon;
  int unsigned                    tst_len;

  // empty array
  logic [8-1:0] nul [];

  // response
  logic [tcb_man.BUS_BEN-1:0][8-1:0] rdt;  // read data
  tcb_rsp_sts_t                      sts;  // status response

////////////////////////////////////////////////////////////////////////////////
// tests
////////////////////////////////////////////////////////////////////////////////

  task test_aligned ();
    // write sequence
    $display("write sequence");
    testname = "write";
    tst_mon.delete();
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
    tst_ref.delete();
    tst_len = tst_ref.size();
    // append reference transfers to queue               ndn       , adr         , wdt                           ,        rdt
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000010, '{8'h10                     }}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000011, '{       8'h32              }}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000012, '{              8'h54       }}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000013, '{                     8'h76}}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000020, '{8'h10, 8'h32              }}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000022, '{              8'h54, 8'h76}}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000030, '{8'h10, 8'h32, 8'h54, 8'h76}}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    // compare transfers from monitor to reference
    // wildcard operator is used to ignore data byte comparison, when the reference data is 8'hxx
    foreach(tst_ref[i]) begin
      assert (tst_mon[i].req ==? tst_ref[i].req) else $error("\ntst_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_mon[i].req, i, tst_ref[i].req);
      assert (tst_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_mon[i].rsp, i, tst_ref[i].rsp);
    end
    // printout transfer queue for debugging purposes
//    foreach (tst_ref[i]) begin
//      $display("DEBUG: tst_mon[%0d] = %p", i, tst_mon[i]);
//      $display("DEBUG: tst_ref[%0d] = %p", i, tst_ref[i]);
//    end

    // read sequence
    $display("read sequence");
    testname = "read";
    tst_mon.delete();
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
    tst_ref.delete();
    tst_len = tst_ref.size();
    // append reference transfers to queue               ndn        , adr         , wdt ,        rdt
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000010, nul}, rsp: '{'{8'h10                     }, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000011, nul}, rsp: '{'{       8'h32              }, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000012, nul}, rsp: '{'{              8'h54       }, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000013, nul}, rsp: '{'{                     8'h76}, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000020, nul}, rsp: '{'{8'h10, 8'h32              }, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000022, nul}, rsp: '{'{              8'h54, 8'h76}, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000030, nul}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}});
    // compare transfers from monitor to reference
    // wildcard operator is used to ignore data byte comparison, when the reference data is 8'hxx
    foreach(tst_ref[i]) begin
      assert (tst_mon[i].req ==? tst_ref[i].req) else $error("\ntst_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_mon[i].req, i, tst_ref[i].req);
      assert (tst_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_mon[i].rsp, i, tst_ref[i].rsp);
    end
//    // printout transfer queue for debugging purposes
//    foreach (tst_ref[i]) begin
//      $display("DEBUG: tst_mon[%0d] = %p", i, tst_mon[i]);
//      $display("DEBUG: tst_ref[%0d] = %p", i, tst_ref[i]);
//    end

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
  endtask: test_aligned

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  always #(20ns/2) clk = ~clk;

  // test sequence
  initial
  begin: test
    // reset sequence
    repeat (2) @(posedge clk);
    rst <= 1'b0;
    repeat (1) @(posedge clk);

    test_aligned;

    // end of test
    repeat (4) @(posedge clk);
    $finish();
  end: test

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  tcb_vip_protocol_checker chk_man (
    .tcb (tcb_man)
  );

  tcb_vip_protocol_checker chk_sub (
    .tcb (tcb_sub)
  );

  // CRAM memory model subordinate
  cram_model #(
    .ADR (tcb_sub.BUS.ADR),
    .DAT (tcb_sub.BUS.DAT),
    .SIZ (2**5)
  ) cram (
    .clk (tcb_sub.clk),
    .wen (tcb_sub.req.wen & tcb_sub.trn),
    .adr (tcb_sub.req.adr),
    .wdt (tcb_sub.req.wdt),
    .rdt (tcb_sub.rsp.rdt)
  );

  assign tcb_sub.rdy = 1'b1;
  assign tcb_sub.rsp.sts = '0;

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

  tcb_lib_read_modify_write dut (
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

endmodule: tcb_lib_read_modify_write_tb
