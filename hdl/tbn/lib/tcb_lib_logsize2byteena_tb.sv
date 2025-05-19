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
  parameter  int unsigned      DLY = TCB_HSK_DEF.DLY      // response delay
//  // bus parameters
//  parameter  tcb_bus_channel_t BUS_CHN = TCB_BUS_DEF.CHN,  // channel configuration
//  parameter  tcb_bus_mode_t    BUS_MOD = TCB_BUS_DEF.MOD,  // manager     data position mode
//  // data packing parameters for manager/subordinate
//  parameter  int unsigned      BUS_ALN = TCB_BUS_DEF.ALN,  // TODO
//  parameter  int unsigned      BUS_MIN = TCB_BUS_DEF.MIN,  // TODO
//  parameter  int unsigned      BUS_OFF = TCB_BUS_DEF.OFF,  // TODO
//  parameter  tcb_bus_order_t   PCK_ORD = TCB_BUS_DEF.ORD   // manager     byte order
);

  // handshake parameter
  localparam tcb_hsk_t HSK = TCB_HSK_DEF;

  // bus parameter
  localparam tcb_bus_t BUS_SIZ = '{
    ADR: TCB_BUS_DEF.ADR,
    DAT: TCB_BUS_DEF.DAT,
    FRM: TCB_BUS_DEF.FRM,
    CHN: TCB_CHN_HALF_DUPLEX,
    PRF: TCB_PRF_DISABLED,
    NXT: TCB_NXT_DISABLED,
    MOD: TCB_MOD_LOG_SIZE,
    ORD: TCB_ORD_DESCENDING,
    NDN: TCB_NDN_BI_NDN
  };

  // bus parameter
  localparam tcb_bus_t BUS_BEN = '{
    ADR: TCB_BUS_DEF.ADR,
    DAT: TCB_BUS_DEF.DAT,
    FRM: TCB_BUS_DEF.FRM,
    CHN: TCB_CHN_HALF_DUPLEX,
    PRF: TCB_PRF_DISABLED,
    NXT: TCB_NXT_DISABLED,
    MOD: TCB_MOD_BYTE_ENA,
    ORD: TCB_ORD_DESCENDING,
    NDN: TCB_NDN_BI_NDN
  };

  // physical interface parameter default
  localparam tcb_pck_t PCK = '{
    MIN: 0,
    OFF: 0,
    ALN: 0,
    BND: 0
  };

  localparam tcb_vip_t VIP = '{
    DRV: 1'b1,
    HLD: 1'b0
  };

//  typedef tcb_c #(HSK, BUS_SIZ, PCK)::req_t req_t;
//  typedef tcb_c #(HSK, BUS_SIZ, PCK)::rsp_t rsp_t;

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
  tcb_if #(tcb_hsk_t, HSK, tcb_bus_t, BUS_SIZ, tcb_pck_t, PCK, req_t, rsp_t                ) tcb_man       (.clk (clk), .rst (rst));
  tcb_if #(tcb_hsk_t, HSK, tcb_bus_t, BUS_BEN, tcb_pck_t, PCK, req_t, rsp_t                ) tcb_sub       (.clk (clk), .rst (rst));
  tcb_if #(tcb_hsk_t, HSK, tcb_bus_t, BUS_BEN, tcb_pck_t, PCK, req_t, rsp_t, tcb_vip_t, VIP) tcb_mem [0:0] (.clk (clk), .rst (rst));

  // parameterized class specialization
  typedef tcb_vip_blocking_c #(tcb_hsk_t, HSK, tcb_bus_t, BUS_SIZ, tcb_pck_t, PCK, req_t, rsp_t) tcb_vip_siz_s;
  typedef tcb_vip_blocking_c #(tcb_hsk_t, HSK, tcb_bus_t, BUS_BEN, tcb_pck_t, PCK, req_t, rsp_t) tcb_vip_ben_s;

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
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000010, '{8'h10                     }}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000011, '{       8'h32              }}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000012, '{              8'h54       }}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000013, '{                     8'h76}}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000020, '{8'h10, 8'h32              }}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000022, '{              8'h54, 8'h76}}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000030, '{8'h10, 8'h32, 8'h54, 8'h76}}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
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
    tst_len += {obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000010, nul}, rsp: '{'{8'h10                     }, sts}})};  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += {obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000011, nul}, rsp: '{'{       8'h32              }, sts}})};  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += {obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000012, nul}, rsp: '{'{              8'h54       }, sts}})};  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += {obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000013, nul}, rsp: '{'{                     8'h76}, sts}})};  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += {obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000020, nul}, rsp: '{'{8'h10, 8'h32              }, sts}})};  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += {obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000022, nul}, rsp: '{'{              8'h54, 8'h76}, sts}})};  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += {obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000030, nul}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}})};  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
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

  task test_misaligned ();
    // clear memory
    mem.mem = '{default: 'x};

    // misaligned write sequence
    $display("misaligned write sequence");
    testname = "misaligned write";
    tst_mon.delete();
    tst_ref.delete();
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
    tst_ref.delete();
    tst_len = tst_ref.size();
    // append reference transfers to queue               ndn       , adr         , wdt                           ,        rdt
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000011, '{8'h10, 8'h32              }}, rsp: '{nul, sts}});
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000023, '{8'h54, 8'h76              }}, rsp: '{nul, sts}});
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000031, '{8'h10, 8'h32, 8'h54, 8'h76}}, rsp: '{nul, sts}});
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000042, '{8'h10, 8'h32, 8'h54, 8'h76}}, rsp: '{nul, sts}});
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000053, '{8'h10, 8'h32, 8'h54, 8'h76}}, rsp: '{nul, sts}});
    // compare transfers from monitor to reference
    // wildcard operator is used to ignore data byte comparison, when the reference data is 8'hxx
    foreach (tst_ref[i]) begin
      assert (tst_mon[i].req ==? tst_ref[i].req) else $error("\ntst_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_mon[i].req, i, tst_ref[i].req);
      assert (tst_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_mon[i].rsp, i, tst_ref[i].rsp);
    end
//    // printout transfer queue for debugging purposes
//    foreach (tst_ref[i]) begin
//      $display("DEBUG: tst_mon[%0d] = %p", i, tst_mon[i]);
//      $display("DEBUG: tst_ref[%0d] = %p", i, tst_ref[i]);
//    end

    // misaligned read/check sequence
    $display("misaligned read/check sequence");
    testname = "misaligned read/check";
    tst_mon.delete();
    tst_ref.delete();
    // test sequence
    fork
      // manager (blocking API)
      begin: fork_man_misaligned_read
        obj_man.check16(32'h00000011, 16'h3210    , sts);
        obj_man.check16(32'h00000023, 16'h7654    , sts);
        obj_man.check32(32'h00000031, 32'h76543210, sts);
        obj_man.check32(32'h00000042, 32'h76543210, sts);
        obj_man.check32(32'h00000053, 32'h76543210, sts);
      end: fork_man_misaligned_read
      // subordinate (monitor)
      begin: fork_mon_misaligned_read
        obj_sub.transfer_monitor(tst_mon);
      end: fork_mon_misaligned_read
    join_any
    // disable transfer monitor
    @(posedge clk);
    disable fork;
    // reference transfer queue
    sts = '0;
    tst_ref.delete();
    tst_len = tst_ref.size();
    // append reference transfers to queue               ndn       , adr         , wdt ,        rdt
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000011, nul}, rsp: '{'{8'h10, 8'h32              }, sts}});
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000023, nul}, rsp: '{'{8'h54, 8'h76              }, sts}});
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000031, nul}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}});
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000042, nul}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}});
    tst_len += obj_sub.set_transaction(tst_ref, '{req: '{TCB_LITTLE, 32'h00000053, nul}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}});
    // compare transfers from monitor to reference
    // wildcard operator is used to ignore data byte comparison, when the reference data is 8'hxx
    foreach (tst_ref[i]) begin
      assert (tst_mon[i].req ==? tst_ref[i].req) else $error("\ntst_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_mon[i].req, i, tst_ref[i].req);
      assert (tst_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_mon[i].rsp, i, tst_ref[i].rsp);
    end
//    // printout transfer queue for debugging purposes
//    foreach (tst_ref[i]) begin
//      $display("DEBUG: tst_mon[%0d] = %p", i, tst_mon[i]);
//      $display("DEBUG: tst_ref[%0d] = %p", i, tst_ref[i]);
//    end
  endtask: test_misaligned

  task test_parameterized();
    static bit ndn_list [2] = '{TCB_LITTLE, TCB_BIG};
//    static bit ndn_list [1] = '{TCB_BIG};
    // parameterized tests
    $display("parameterized tests");
    testname = "parameterized tests";
    foreach (ndn_list[i]) begin
      for (int unsigned siz=tcb_man.PCK.MIN; siz<=tcb_man.BUS_MAX; siz++) begin
//      begin
//        static int unsigned siz=1;
//        for (int unsigned off=0; off<tcb_man.BUS_BEN; off+=2) begin
        for (int unsigned off=0; off<tcb_man.BUS_BEN; off+=2**tcb_man.PCK.OFF) begin
          // local variables
          string       id;
          int unsigned size;
          int unsigned len;
          // address
          logic [tcb_man.BUS.ADR-1:0] adr;
          // endianness
          logic         ndn;
          // local data arrays
          logic [8-1:0] dat [];  // pattern   data array
          logic [8-1:0] tmp [];  // temporary data array
          logic [8-1:0] nul [];  // empty     data array
          // local response
          tcb_rsp_sts_t sts;  // response status
          // local transactions
          tcb_vip_siz_s::transaction_t transaction_ref_w;  // reference write transaction
          tcb_vip_siz_s::transaction_t transaction_ref_r;  // reference read  transaction
          tcb_vip_siz_s::transaction_t transaction_mon_w;  // monitor   write transaction
          tcb_vip_siz_s::transaction_t transaction_mon_r;  // monitor   read  transaction
          // local transfers
          automatic tcb_vip_siz_s::transfer_queue_t transfer_man = '{};  // manager     transfer queue
          automatic tcb_vip_siz_s::transfer_queue_t transfer_sub = '{};  // subordinate transfer queue
          automatic tcb_vip_siz_s::transfer_queue_t transfer_mon = '{};  // monitor     transfer queue

          // endianness
          ndn = ndn_list[i];
          // ID
          id = $sformatf("ndn=%0d siz=%0d off=%0d", ndn, siz, off);
          $display("DEBUG: ID = '%s'", id);
          // address (stride is twice BUS_BEN, to accommodate unaligned accesses)
          adr = siz * tcb_man.BUS_BEN * 2;
          // prepare data array
          size = 2**siz;
          dat = new[size];
          for (int unsigned i=0; i<size; i++) begin
            // each byte within a transfer has an unique value
            dat[i] = {siz[4-1:0], off[4-1:0] + i[4-1:0]};
          end
          // expected response status
          sts = '0;

          // write/read transaction
          //                           ndn, adr    , wdt          rdt, sts
          transaction_ref_w = '{req: '{ndn, adr+off, dat}, rsp: '{nul, sts}};
          transaction_ref_r = '{req: '{ndn, adr+off, nul}, rsp: '{dat, sts}};
          // manager transfer queue
          len  = 0;
          len += obj_man.set_transaction(transfer_man, transaction_ref_w, id);
          len += obj_man.set_transaction(transfer_man, transaction_ref_r, id);
          // subordinate transfer queue
          len  = 0;
          len += obj_sub.set_transaction(transfer_sub, transaction_ref_w);
          len += obj_sub.set_transaction(transfer_sub, transaction_ref_r);

          // play/monitor transfers
          fork
            // drive manager bus
            begin: parameterized_test_man
              obj_man.transfer_sequencer(transfer_man);
            end: parameterized_test_man
            // monitor subordinate bus
            begin: parameterized_test_mon
              obj_sub.transfer_monitor(transfer_mon);
            end: parameterized_test_mon
          join_any
          // disable transfer monitor
          @(posedge clk);
          disable fork;

          // parse manager transfer queues into transactions
          len  = 0;
          len += obj_man.get_transaction(transfer_man, transaction_mon_w);
          len += obj_man.get_transaction(transfer_man, transaction_mon_r);
          // compare read data against write data
          assert (transaction_mon_r.rsp.rdt == dat) else $error("Read data not matching previously written data (id = '%s')", id);
          // compare subordinate reference and monitored transaction queue
          foreach (transfer_sub[i]) begin
            assert (transfer_mon[i].req ==? transfer_sub[i].req) else $error("\ntransfer_mon[%0d].req = %p !=? \ntransfer_ref[%0d].req = %p", i, transfer_mon[i].req, i, transfer_sub[i].req);
            assert (transfer_mon[i].rsp ==? transfer_sub[i].rsp) else $error("\ntransfer_mon[%0d].rsp = %p !=? \ntransfer_ref[%0d].rsp = %p", i, transfer_mon[i].rsp, i, transfer_sub[i].rsp);
          end
          // parse subordinate monitor transfer queues into transactions
          len  = 0;
          len += obj_sub.get_transaction(transfer_mon, transaction_mon_w);
          len += obj_sub.get_transaction(transfer_mon, transaction_mon_r);
          // compare subordinate reference and monitor transactions
          assert (transaction_mon_w == transaction_ref_w) else $error("\ntransaction_mon_w = %p != \ntransaction_ref_w = %p", transaction_mon_w, transaction_ref_w);
          assert (transaction_mon_r == transaction_ref_r) else $error("\ntransaction_mon_r = %p != \ntransaction_ref_r = %p", transaction_mon_r, transaction_ref_r);
        end
      end
    end
  endtask: test_parameterized

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

    obj_man.write8 (32'h00000010,        8'h10, sts);
    obj_man.read8  (32'h00000010, rdt[1-1:0], sts);


//    test_aligned;
//    if (PCK.ALN != tcb_man.BUS_MAX) begin
//      test_misaligned;
//    end
//    test_parameterized;

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

  tcb_vip_protocol_checker chk_man (
    .tcb (tcb_man)
  );

  tcb_vip_protocol_checker chk_sub (
    .tcb (tcb_sub)
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
