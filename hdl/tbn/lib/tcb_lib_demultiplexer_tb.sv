////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library demultiplexer/decoder testbench
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
  parameter  int unsigned IFL = $clog2(IFN)
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

  // decoder address and mask array
  localparam logic [ADR-1:0] DAM [IFN-1:0] = '{
    ADR'({14'bx, 2'b1x, 16'hxxxx}),
    ADR'({14'bx, 2'b01, 16'hxxxx}),
    ADR'({14'bx, 2'b00, 16'hxxxx})
  };

  localparam tcb_cfg_t CFG = '{
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
  tcb_if #(tcb_cfg_t, CFG, req_t, rsp_t                ) tcb_man           (.clk (clk), .rst (rst));
  tcb_if #(tcb_cfg_t, CFG, req_t, rsp_t, tcb_vip_t, VIP) tcb_sub [IFN-1:0] (.clk (clk), .rst (rst));

  // parameterized class specialization (blocking API)
  typedef tcb_vip_blocking_c #(tcb_cfg_t, CFG, req_t, rsp_t                ) tcb_man_s;
  typedef tcb_vip_blocking_c #(tcb_cfg_t, CFG, req_t, rsp_t, tcb_vip_t, VIP) tcb_sub_s;

  // TCB class objects
  tcb_man_s obj_man = new(tcb_man, "MAN");
  tcb_sub_s obj_sub [IFN];

  // transfer reference/monitor array
  tcb_sub_s::transfer_queue_t tst_sub [IFN];
  tcb_sub_s::transfer_queue_t tst_mon [IFN];
  int unsigned                tst_len;

  // empty array
  logic [8-1:0] nul [];

  // response
  logic [tcb_man.CFG_BUS_BYT-1:0][8-1:0] rdt;  // read data
  tcb_rsp_sts_t                          sts;  // status response

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
      tst_sub[i].delete();
      tst_mon[i].delete();
    end
    fork
      // manager (blocking API)
      begin: fork_man
        for (int unsigned i=0; i<IFN; i++) begin
          obj_man.write32((i<<16) + 32'h00000000, 32'h76543210, sts);
          obj_man.write32((i<<16) + 32'h00000020, 32'hfedcba98, sts);
          obj_man.read32 ((i<<16) + 32'h00000000, rdt[4-1:0], sts);
          obj_man.read32 ((i<<16) + 32'h00000020, rdt[4-1:0], sts);
        end
      end: fork_man
      // subordinate (driver)
      for (int unsigned i=0; i<IFN; i++)
      begin: fork_sub_driver
        sts[i] = '0;
        tst_len[i] = tst_sub[i].size();
        // append reference transfers to queue                        adr                wdt
        tst_len[i] += obj_sub[i].put_transaction(tst_sub[i], '{req: '{adr: 32'h00000000, wdt: '{8'h10, 8'h32, 8'h54, 8'h76}, default: 'x}, rsp: '{nul, sts}});
        tst_len[i] += obj_sub[i].put_transaction(tst_sub[i], '{req: '{adr: 32'h00000020, wdt: '{8'h98, 8'hba, 8'hdc, 8'hfe}, default: 'x}, rsp: '{nul, sts}});
        tst_len[i] += obj_sub[i].put_transaction(tst_sub[i], '{req: '{adr: 32'h00000000, wdt: nul, default: 'x}, rsp: '{'{8'h10, 8'h32, 8'h54, 8'h76}, sts}});
        tst_len[i] += obj_sub[i].put_transaction(tst_sub[i], '{req: '{adr: 32'h00000020, wdt: nul, default: 'x}, rsp: '{'{8'h98, 8'hba, 8'hdc, 8'hfe}, sts}});
//        for (int unsigned j=0; j<tst_sub[i].size(); j++) begin
//          $display("DEBUG: tst_sub[%0d][%0d] = %p", i, j, tst_sub[i][j]);
//        end
        obj_sub[i].transfer_sequencer(tst_sub[i]);
      end: fork_sub_driver
      // subordinate (monitor)
      for (int unsigned i=0; i<IFN; i++)
      begin: fork_sub_monitor
        obj_sub[i].transfer_monitor(tst_mon[i]);
      end: fork_sub_monitor
    join_any
    // disable transfer monitor
    repeat (tcb_man.CFG.HSK.DLY) @(posedge clk);
    disable fork;
    // reference transfer queue
    for (int unsigned i=0; i<IFN; i++)
    begin
      // compare transfers from monitor to reference
      // wildcard operator is used to ignore data byte comparison, when the reference data is 8'hxx
      for (int unsigned j=0; j<tst_sub[i].size(); j++) begin
        assert (tst_mon[i][j].req ==? tst_sub[i][j].req) else $error("\ntst_mon[%0d][%0d].req = %p !=? \ntst_sub[%0d][%0d].req = %p", i, j, tst_mon[i][j].req, i, j, tst_sub[i][j].req);
        assert (tst_mon[i][j].rsp ==? tst_sub[i][j].rsp) else $error("\ntst_mon[%0d][%0d].rsp = %p !=? \ntst_sub[%0d][%0d].rsp = %p", i, j, tst_mon[i][j].rsp, i, j, tst_sub[i][j].rsp);
      end
//      // printout transfer queue for debugging purposes
//      for (int unsigned j=0; j<tst_sub[i].size(); j++) begin
//        $display("DEBUG: tst_sub[%0d][%0d] = %p", i, j, tst_sub[i][j]);
//        $display("DEBUG: tst_mon[%0d][%0d] = %p", i, j, tst_mon[i][j]);
//      end
    end
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
      obj_sub[i] = new(tcb_sub[i], "SUB");
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

  tcb_vip_protocol_checker chk_sub [IFN-1:0] (
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
  ) dut_dec (
    .tcb  (tcb_man),
    .sel  (sel)
  );

  // RTL demultiplexer DUT
  tcb_lib_demultiplexer #(
    // interconnect parameters
    .IFN   (IFN)
  ) dut_dmx (
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
