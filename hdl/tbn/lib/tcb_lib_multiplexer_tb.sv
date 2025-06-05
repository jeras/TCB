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
  parameter  int unsigned IFL = $clog2(IFN)
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  // interface priorities (lower number is higher priority)
  localparam int unsigned PRI [IFN-1:0] = '{2, 1, 0};

  // handshake parameter
  localparam tcb_hsk_t CFG.HSK = TCB_HSK_DEF;

  // bus parameter
  localparam tcb_bus_t BUS = '{
    ADR: TCB_BUS_DEF.ADR,
    DAT: TCB_BUS_DEF.DAT,
    FRM: TCB_BUS_DEF.FRM,
    CHN: TCB_CHN_HALF_DUPLEX,
    AMO: TCB_AMO_ABSENT,
    PRF: TCB_PRF_ABSENT,
    NXT: TCB_NXT_ABSENT,
    MOD: TCB_MOD_LOG_SIZE,
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
  tcb_if #(tcb_hsk_t, CFG.HSK, tcb_bus_t, BUS, tcb_pma_t, PMA, req_t, rsp_t                ) tcb_man [IFN-1:0] (.clk (clk), .rst (rst));
  tcb_if #(tcb_hsk_t, CFG.HSK, tcb_bus_t, BUS, tcb_pma_t, PMA, req_t, rsp_t, tcb_vip_t, VIP) tcb_sub           (.clk (clk), .rst (rst));

  // parameterized class specialization (blocking API)
  typedef tcb_vip_blocking_c #(tcb_hsk_t, CFG.HSK, tcb_bus_t, BUS, tcb_pma_t, PMA, req_t, rsp_t                ) tcb_man_s;
  typedef tcb_vip_blocking_c #(tcb_hsk_t, CFG.HSK, tcb_bus_t, BUS, tcb_pma_t, PMA, req_t, rsp_t, tcb_vip_t, VIP) tcb_sub_s;

  // TCB class objects
  tcb_man_s obj_man [IFN];
  tcb_sub_s obj_sub = new(tcb_sub, "SUB");

  // transfer reference/monitor array
  tcb_sub_s::transfer_queue_t tst_sub;
  tcb_sub_s::transfer_queue_t tst_mon;
  int unsigned                tst_len;

  // empty array
  logic [8-1:0] nul [];

  // response
  logic [tcb_sub.BUS_BYT-1:0][8-1:0] rdt_man [IFN];  // read data
  tcb_rsp_sts_t                      sts_man [IFN];  // status response
  tcb_rsp_sts_t                      sts_sub;  // status response

  // control
  logic [IFL-1:0] sel;  // select

////////////////////////////////////////////////////////////////////////////////
// tests
////////////////////////////////////////////////////////////////////////////////

  task test_simple ();
    // write sequence
    $display("write sequence");
    testname = "write";
    tst_mon.delete();
    fork
      // manager (blocking API)
      begin: fork_man
        fork
          obj_man[0].write32(0*tcb_sub.BUS_BYT, {4{8'd0}}, sts_man[0]);
          obj_man[1].write32(1*tcb_sub.BUS_BYT, {4{8'd1}}, sts_man[1]);
          obj_man[2].write32(2*tcb_sub.BUS_BYT, {4{8'd2}}, sts_man[2]);
        join
        fork
          obj_man[0].read32 (0*tcb_sub.BUS_BYT, rdt_man[0][4-1:0], sts_man[0]);
          obj_man[1].read32 (1*tcb_sub.BUS_BYT, rdt_man[1][4-1:0], sts_man[1]);
          obj_man[2].read32 (2*tcb_sub.BUS_BYT, rdt_man[2][4-1:0], sts_man[2]);
        join
//        for (int unsigned i=0; i<IFN; i++) begin: fork_write
//          fork
//            obj_man[i].write32(i*tcb_sub.BUS_BYT, {4{8'(i)}}, sts_man[i]);
//          join_none
//        end: fork_write
//        wait fork;
//        for (int unsigned i=0; i<IFN; i++) begin: fork_read
//          fork
//            obj_man[i].read32(i*tcb_sub.BUS_BYT, rdt_man[i][4-1:0], sts_man[i]);
//          join_none
//        end: fork_read
//        wait fork;
      end: fork_man
      // subordinate (driver)
      begin: fork_sub_driver
        tst_sub.delete();
        sts_sub = '0;
        tst_len = tst_sub.size();
        for (int unsigned i=0; i<IFN; i++) begin: write
          // append reference transfers to queue               ndn       , adr              , wdt        ,        rdt
          tst_len += obj_sub.put_transaction(tst_sub, '{req: '{TCB_LITTLE, i*tcb_sub.BUS_BYT, '{4{8'(i)}}}, rsp: '{nul, sts_sub}});
        end: write
        for (int unsigned i=0; i<IFN; i++) begin: read
          // append reference transfers to queue               ndn       , adr              , wdt ,        rdt
          tst_len += obj_sub.put_transaction(tst_sub, '{req: '{TCB_LITTLE, i*tcb_sub.BUS_BYT, nul}, rsp: '{'{4{8'(i)}}, sts_sub}});
        end: read
        obj_sub.transfer_sequencer(tst_sub);
      end: fork_sub_driver
      // subordinate (monitor)
      begin: fork_sub_monitor
        obj_sub.transfer_monitor(tst_mon);
      end: fork_sub_monitor
    join_any
    // disable transfer monitor
    @(posedge clk);
    disable fork;
    // compare transfers from monitor to reference
    // wildcard operator is used to ignore data byte comparison, when the reference data is 8'hxx
    foreach (tst_sub[i]) begin
      assert (tst_mon[i].req ==? tst_sub[i].req) else $error("\ntst_mon[%0d].req = %p !=? \ntst_sub[%0d].req = %p", i, tst_mon[i].req, i, tst_sub[i].req);
      assert (tst_mon[i].rsp ==? tst_sub[i].rsp) else $error("\ntst_mon[%0d].rsp = %p !=? \ntst_sub[%0d].rsp = %p", i, tst_mon[i].rsp, i, tst_sub[i].rsp);
    end
//    // printout transfer queue for debugging purposes
//    foreach (tst_sub[i]) begin
//      $display("DEBUG: tst_sub[%0d] = %p", i, tst_sub[i]);
//      $display("DEBUG: tst_mon[%0d] = %p", i, tst_mon[i]);
//    end
  endtask: test_simple

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  always #(20ns/2) clk = ~clk;

  // initialize subordinate objects
  generate
  for (genvar i=0; i<IFN; i++) begin
    initial begin    
      obj_man[i] = new(tcb_man[i], "MAN");
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
// VIP component instances
////////////////////////////////////////////////////////////////////////////////

  tcb_vip_protocol_checker chk_man [IFN-1:0] (
    .tcb (tcb_man)
  );

  tcb_vip_protocol_checker chk_sub (
    .tcb (tcb_sub)
  );

////////////////////////////////////////////////////////////////////////////////
// DUT instances
////////////////////////////////////////////////////////////////////////////////

  // RTL arbiter DUT
  tcb_lib_arbiter #(
    // arbitration priority mode
//  .MD   (),
    // interconnect parameters
    .IFN  (IFN),
    // interface priorities (lower number is higher priority)
    .PRI  (PRI)
  ) dut_arb (
    .tcb  (tcb_man),
    .sel  (sel)
  );

  // RTL multiplexer DUT
  tcb_lib_multiplexer #(
    // interconnect parameters
    .IFN   (IFN)
  ) dut_mux (
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

endmodule: tcb_lib_multiplexer_tb
