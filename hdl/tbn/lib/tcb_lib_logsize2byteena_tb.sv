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
//  // PMA parameters for manager/subordinate
//  parameter  int unsigned      BUS_ALN = TCB_BUS_DEF.ALN,  // TODO
//  parameter  int unsigned      BUS_MIN = TCB_BUS_DEF.MIN,  // TODO
//  parameter  int unsigned      BUS_OFF = TCB_BUS_DEF.OFF,  // TODO
//  parameter  tcb_bus_order_t   PMA_ORD = TCB_BUS_DEF.ORD   // manager     byte order
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  localparam tcb_cfg_t CFG_SIZ = '{
    // handshake parameter
    HSK: TCB_HSK_DEF,
    // bus parameter
    BUS: '{
      ADR: TCB_BUS_DEF.ADR,
      DAT: TCB_BUS_DEF.DAT,
      LEN: TCB_BUS_DEF.LEN,
      LCK: TCB_LCK_PRESENT,
      CHN: TCB_CHN_HALF_DUPLEX,
      AMO: TCB_AMO_ABSENT,
      PRF: TCB_PRF_ABSENT,
      NXT: TCB_NXT_ABSENT,
      MOD: TCB_MOD_LOG_SIZE,
      ORD: TCB_ORD_DESCENDING,
      NDN: TCB_NDN_BI_NDN
    },
    // physical interface parameter default
    PMA: TCB_PMA_DEF
  };

  localparam tcb_cfg_t CFG_BYT = '{
    // handshake parameter
    HSK: TCB_HSK_DEF,
    // bus parameter
    BUS: '{
      ADR: TCB_BUS_DEF.ADR,
      DAT: TCB_BUS_DEF.DAT,
      LEN: TCB_BUS_DEF.LEN,
      LCK: TCB_LCK_PRESENT,
      CHN: TCB_CHN_HALF_DUPLEX,
      AMO: TCB_AMO_ABSENT,
      PRF: TCB_PRF_ABSENT,
      NXT: TCB_NXT_ABSENT,
      MOD: TCB_MOD_BYTE_ENA,
      ORD: TCB_ORD_DESCENDING,
      NDN: TCB_NDN_BI_NDN
    },
    // physical interface parameter default
    PMA: TCB_PMA_DEF
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
  tcb_if #(tcb_cfg_t, CFG_SIZ, req_t, rsp_t                ) tcb_man       (.clk (clk), .rst (rst));
  tcb_if #(tcb_cfg_t, CFG_BYT, req_t, rsp_t                ) tcb_sub       (.clk (clk), .rst (rst));
  tcb_if #(tcb_cfg_t, CFG_BYT, req_t, rsp_t, tcb_vip_t, VIP) tcb_mem [0:0] (.clk (clk), .rst (rst));

  // parameterized class specialization (blocking API)
  typedef tcb_vip_blocking_c #(tcb_cfg_t, CFG_SIZ, req_t, rsp_t) tcb_siz_s;
  typedef tcb_vip_blocking_c #(tcb_cfg_t, CFG_BYT, req_t, rsp_t) tcb_byt_s;

  // TCB class objects
  tcb_siz_s obj_man = new(tcb_man, "MAN");
  tcb_byt_s obj_sub = new(tcb_sub, "MON");

  // transfer reference/monitor array
  tcb_byt_s::transfer_queue_t tst_ref;
  tcb_byt_s::transfer_queue_t tst_mon;
  int unsigned                tst_len;

  // empty array
  logic [8-1:0] nul [];

  // response
  logic [tcb_man.CFG_BUS_BYT-1:0][8-1:0] rdt;  // read data
  tcb_rsp_sts_t                          sts;  // status response

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
    // append reference transfers to queue               adr              , wdt                                             ,        rdt
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000010, wdt: '{8'h10                     }, default: 'x}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000011, wdt: '{       8'h32              }, default: 'x}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000012, wdt: '{              8'h54       }, default: 'x}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000013, wdt: '{                     8'h76}, default: 'x}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000020, wdt: '{8'h10, 8'h32              }, default: 'x}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000022, wdt: '{              8'h54, 8'h76}, default: 'x}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000030, wdt: '{8'h10, 8'h32, 8'h54, 8'h76}, default: 'x}, rsp: '{nul, sts}});  //$display("DEBUG: tst_ref.size() = %0d", tst_ref.size());
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
    // append reference transfers to queue               adr              , wdt                   ,        rdt
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000010, wdt: nul, default: 'x}, rsp: '{'{8'h10                     }, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000011, wdt: nul, default: 'x}, rsp: '{'{       8'h32              }, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000012, wdt: nul, default: 'x}, rsp: '{'{              8'h54       }, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000013, wdt: nul, default: 'x}, rsp: '{'{                     8'h76}, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000020, wdt: nul, default: 'x}, rsp: '{'{8'h10, 8'h32              }, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000022, wdt: nul, default: 'x}, rsp: '{'{              8'h54, 8'h76}, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000030, wdt: nul, default: 'x}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}});
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
    // append reference transfers to queue               adr              , wdt                                             ,        rdt
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000011, wdt: '{8'h10, 8'h32              }, default: 'x}, rsp: '{nul, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000023, wdt: '{8'h54, 8'h76              }, default: 'x}, rsp: '{nul, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000031, wdt: '{8'h10, 8'h32, 8'h54, 8'h76}, default: 'x}, rsp: '{nul, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000042, wdt: '{8'h10, 8'h32, 8'h54, 8'h76}, default: 'x}, rsp: '{nul, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000053, wdt: '{8'h10, 8'h32, 8'h54, 8'h76}, default: 'x}, rsp: '{nul, sts}});
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
    // append reference transfers to queue               adr              , wdt                   ,        rdt
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000011, wdt: nul, default: 'x}, rsp: '{'{8'h10, 8'h32              }, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000023, wdt: nul, default: 'x}, rsp: '{'{8'h54, 8'h76              }, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000031, wdt: nul, default: 'x}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000042, wdt: nul, default: 'x}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}});
    tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h00000053, wdt: nul, default: 'x}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}});
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
      for (int unsigned siz=tcb_man.CFG.PMA.MIN; siz<=tcb_man.CFG_BUS_MAX; siz++) begin
//      begin
//        static int unsigned siz=1;
//        for (int unsigned off=0; off<tcb_man.CFG_BUS_BYT; off+=2) begin
        for (int unsigned off=0; off<tcb_man.CFG_BUS_BYT; off+=2**tcb_man.CFG.PMA.OFF) begin
          // local variables
          string       id;
          int unsigned size;
          int unsigned len;
          // address
          logic [tcb_man.CFG.BUS.ADR-1:0] adr;
          // endianness
          logic         ndn;
          // local data arrays
          logic [8-1:0] dat [];  // pattern   data array
          logic [8-1:0] tmp [];  // temporary data array
          logic [8-1:0] nul [];  // empty     data array
          // local response
          tcb_rsp_sts_t sts;  // response status
          // local transactions
          tcb_siz_s::transaction_t transaction_man_w;  // manager     write transaction
          tcb_siz_s::transaction_t transaction_man_r;  // manager     read  transaction
          tcb_byt_s::transaction_t transaction_sub_w;  // bubordinate write transaction
          tcb_byt_s::transaction_t transaction_sub_r;  // bubordinate read  transaction
          tcb_byt_s::transaction_t transaction_mon_w;  // monitor     write transaction
          tcb_byt_s::transaction_t transaction_mon_r;  // monitor     read  transaction
          // local transfers
          automatic tcb_siz_s::transfer_queue_t transfer_man = '{};  // manager     transfer queue
          automatic tcb_byt_s::transfer_queue_t transfer_sub = '{};  // subordinate transfer queue
          automatic tcb_byt_s::transfer_queue_t transfer_mon = '{};  // monitor     transfer queue

          // endianness
          ndn = ndn_list[i];
          // ID
          id = $sformatf("ndn=%0d siz=%0d off=%0d", ndn, siz, off);
          $display("DEBUG: ID = '%s'", id);
          // address (stride is twice BUS_BYT, to accommodate unaligned accesses)
          adr = siz * tcb_man.CFG_BUS_BYT * 2;
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
          transaction_man_w = '{req: '{ndn: ndn, adr: adr+off, wdt: dat, default: 'x}, rsp: '{nul, sts}};
          transaction_man_r = '{req: '{ndn: ndn, adr: adr+off, wdt: nul, default: 'x}, rsp: '{dat, sts}};
          transaction_sub_w = '{req: '{ndn: ndn, adr: adr+off, wdt: dat, default: 'x}, rsp: '{nul, sts}};
          transaction_sub_r = '{req: '{ndn: ndn, adr: adr+off, wdt: nul, default: 'x}, rsp: '{dat, sts}};
          // manager transfer queue
          len  = 0;
          len += obj_man.put_transaction(transfer_man, transaction_man_w, id);
          len += obj_man.put_transaction(transfer_man, transaction_man_r, id);
          // subordinate transfer queue
          len  = 0;
          len += obj_sub.put_transaction(transfer_sub, transaction_sub_w);
          len += obj_sub.put_transaction(transfer_sub, transaction_sub_r);

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
          len += obj_man.get_transaction(transfer_man, transaction_man_w);
          len += obj_man.get_transaction(transfer_man, transaction_man_r);
          // compare read data against write data
          assert (transaction_man_r.rsp.rdt == dat) else $error("Read data not matching previously written data (id = '%s')", id);
          // compare subordinate reference and monitored transfer queue
          foreach (transfer_sub[i]) begin
            assert (transfer_mon[i].req ==? transfer_sub[i].req) else $error("\ntransfer_mon[%0d].req = %p !=? \ntransfer_sub[%0d].req = %p", i, transfer_mon[i].req, i, transfer_sub[i].req);
            assert (transfer_mon[i].rsp ==? transfer_sub[i].rsp) else $error("\ntransfer_mon[%0d].rsp = %p !=? \ntransfer_sub[%0d].rsp = %p", i, transfer_mon[i].rsp, i, transfer_sub[i].rsp);
          end
          // parse subordinate monitor transfer queues into transactions
          len  = 0;
          len += obj_sub.get_transaction(transfer_mon, transaction_mon_w);
          len += obj_sub.get_transaction(transfer_mon, transaction_mon_r);
          // compare subordinate reference and monitor transactions
          assert (transaction_mon_w == transaction_sub_w) else $error("\ntransaction_mon_w = %p != \ntransaction_sub_w = %p", transaction_mon_w, transaction_sub_w);
          assert (transaction_mon_r == transaction_sub_r) else $error("\ntransaction_mon_r = %p != \ntransaction_sub_r = %p", transaction_mon_r, transaction_sub_r);
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

    test_aligned;
    if (CFG_SIZ.PMA.ALN != tcb_man.CFG_BUS_MAX) begin
      test_misaligned;
    end
    test_parameterized;

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
