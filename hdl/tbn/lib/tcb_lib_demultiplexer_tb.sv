////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) LIBrary DeMultipleXer/DECoder TestBench
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

module tcb_lib_demultiplexer_tb
  import tcb_pkg::*;
  import tcb_vip_blocking_pkg::*;
#(
  // response delay
  parameter  int unsigned DLY = TCB_HSK_DEF.DLY,
  // TCB widths
  parameter  int unsigned ADR = TCB_BUS_DEF.ADR,       // address bus width
  parameter  int unsigned DAT = TCB_BUS_DEF.DAT,       // data    bus width
  // interconnect parameters (interface number)
  parameter  int unsigned IFN = 3,
  parameter  int unsigned IFL = $clog2(IFN),
  // decoder address and mask array
  parameter  logic [ADR-1:0] DAM [IFN-1:0] = '{IFN{ADR'('x)}}
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  // handshake parameter
  localparam tcb_hsk_t HSK = TCB_HSK_DEF;

  // bus parameter
  localparam tcb_bus_t BUS = '{
    ADR: TCB_BUS_DEF.ADR,
    DAT: TCB_BUS_DEF.DAT,
    FRM: TCB_BUS_DEF.FRM,
    CHN: TCB_CHN_HALF_DUPLEX,
    AMO: TCB_AMO_DISABLED,
    PRF: TCB_PRF_DISABLED,
    NXT: TCB_NXT_DISABLED,
    MOD: TCB_MOD_LOG_SIZE,
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
  tcb_if #(tcb_hsk_t, HSK, tcb_bus_t, BUS, tcb_pck_t, PCK, req_t, rsp_t                ) tcb_man           (.clk (clk), .rst (rst));
  tcb_if #(tcb_hsk_t, HSK, tcb_bus_t, BUS, tcb_pck_t, PCK, req_t, rsp_t, tcb_vip_t, VIP) tcb_sub [0:IFN-1] (.clk (clk), .rst (rst));

  // parameterized class specialization (blocking API)
  typedef tcb_vip_blocking_c #(tcb_hsk_t, HSK, tcb_bus_t, BUS, tcb_pck_t, PCK, req_t, rsp_t                ) tcb_man_s;
  typedef tcb_vip_blocking_c #(tcb_hsk_t, HSK, tcb_bus_t, BUS, tcb_pck_t, PCK, req_t, rsp_t, tcb_vip_t, VIP) tcb_sub_s;

  // TCB class objects
  tcb_man_s obj_man = new(tcb_man, "MAN");
  tcb_sub_s obj_mon [IFN];
  tcb_sub_s obj_sub [IFN];

  // transfer reference/monitor array
  tcb_sub_s::transfer_queue_t tst_man;
  tcb_sub_s::transfer_queue_t tst_sub [IFN];
  tcb_sub_s::transfer_queue_t tst_mon [IFN];
  int unsigned                tst_len;

  // empty array
  logic [8-1:0] nul [];

  // response
  logic [tcb_man.BUS_BEN-1:0][8-1:0] rdt;  // read data
  tcb_rsp_sts_t                      sts;  // status response

  // control
  logic [IFL-1:0] sel;  // select

////////////////////////////////////////////////////////////////////////////////
// tests
////////////////////////////////////////////////////////////////////////////////

  task test_simple ();
    // write sequence
    $display("write sequence");
    testname = "write";
    for (int i=0; i<IFN; i++) begin
      tst_mon[i].delete();
    end
    fork
      // manager (blocking API)
      begin: fork_man
        for (int i=0; i<IFN; i++) begin
          obj_man.write32(i<<16 + 32'h00000000, 32'h76543210, sts);
          obj_man.write32(i<<16 + 32'h00000020, 32'hfedcba98, sts);
          obj_man.read32 (i<<16 + 32'h00000000, rdt[4-1:0], sts);
          obj_man.read32 (i<<16 + 32'h00000020, rdt[4-1:0], sts);
        end
      end: fork_man
      // subordinate (monitor)
      for (int unsigned i=0; i<IFN; i++)
      begin: fork_sub
        obj_sub[i].transfer_monitor(tst_mon[i]);
      end: fork_sub
    join_any
    // disable transfer monitor
    @(posedge clk);
    disable fork;
    // reference transfer queue
    for (int unsigned i=0; i<IFN; i++)
    begin
      automatic tcb_sub_s::transfer_queue_t tmp_sub;
      automatic tcb_sub_s::transfer_queue_t tmp_mon;
      sts[i] = '0;
      tst_sub[i].delete();
      tst_len[i] = tst_sub[i].size();
      // append reference transfers to queue               ndn       , adr         , wdt                           ,        rdt
      tst_len[i] += obj_sub[i].put_transaction(tst_sub[i], '{req: '{TCB_LITTLE, 32'h00000030, '{8'h10, 8'h32, 8'h54, 8'h76}}, rsp: '{nul, sts}});
      tst_len[i] += obj_sub[i].put_transaction(tst_sub[i], '{req: '{TCB_LITTLE, 32'h00000030, nul}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}});
      // compare transfers from monitor to reference
      // wildcard operator is used to ignore data byte comparison, when the reference data is 8'hxx
      tmp_sub = tst_sub[i];
      tmp_mon = tst_mon[i];
      foreach (tmp_sub[i]) begin
        assert (tmp_mon[i].req ==? tmp_sub[i].req) else $error("\ntst_mon[%0d].req = %p !=? \ntst_sub[%0d].req = %p", i, tmp_mon[i].req, i, tmp_sub[i].req);
        assert (tmp_mon[i].rsp ==? tmp_sub[i].rsp) else $error("\ntst_mon[%0d].rsp = %p !=? \ntst_sub[%0d].rsp = %p", i, tmp_mon[i].rsp, i, tmp_sub[i].rsp);
      end
      // printout transfer queue for debugging purposes
//      foreach (tst_sub[i]) begin
//        $display("DEBUG: tst_mon[%0d] = %p", i, tst_mon[i]);
//        $display("DEBUG: tst_sub[%0d] = %p", i, tst_sub[i]);
//      end
    end
  endtask: test_simple


/*
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
          len += obj_man.put_transaction(transfer_man, transaction_ref_w, id);
          len += obj_man.put_transaction(transfer_man, transaction_ref_r, id);
          // subordinate transfer queue
          len  = 0;
          len += obj_sub.put_transaction(transfer_sub, transaction_ref_w);
          len += obj_sub.put_transaction(transfer_sub, transaction_ref_r);

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
*/

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  always #(20ns/2) clk = ~clk;

  // initialize subordinate objects
  generate
  for (genvar i=0; i<IFN; i++) begin
    initial begin    
      obj_sub[i] = new(tcb_sub[i], "SUB");
      obj_mon[i] = new(tcb_sub[i], "MON");
    end
  end
  endgenerate

  // test sequence
  initial
  begin: test
    // reset sequence
    repeat (2) @(posedge clk);
    rst <= 1'b0;
    repeat (1) @(posedge clk);

    test_simple;
//    test_parameterized;

    // end of test
    repeat (4) @(posedge clk);
    $finish();
  end: test

  // timeout
  initial
  begin: timeout
    repeat (20) @(posedge clk);
    $finish();
  end: timeout

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  tcb_vip_protocol_checker chk_man (
    .tcb (tcb_man)
  );

  tcb_vip_protocol_checker chk_sub [0:IFN-1] (
    .tcb (tcb_sub)
  );

////////////////////////////////////////////////////////////////////////////////
// DUT instances
////////////////////////////////////////////////////////////////////////////////

  // RTL decoder DUT
  tcb_lib_decoder #(
    // interconnect parameters
    .IFN  (IFN),
    // decoder address and mask array
    .DAM  (DAM)
  ) arb (
    .tcb  (tcb_man),
    .sel  (sel)
  );

  // RTL demultiplexer DUT
  tcb_lib_demultiplexer #(
    // interconnect parameters
    .IFN   (IFN)
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
`ifdef VERILATOR
    $dumpfile("test.fst");
`else
    $dumpfile("test.vcd");
`endif
    $dumpvars;
  end

endmodule: tcb_lib_demultiplexer_tb
