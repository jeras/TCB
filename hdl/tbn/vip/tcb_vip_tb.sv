////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) manager/monitor/subordinate TestBench
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

module tcb_vip_tb
  import tcb_pkg::*;
  import tcb_vip_transfer_pkg::*;
  import tcb_vip_nonblocking_pkg::*;
  import tcb_vip_blocking_pkg::*;
#(
  // response delay
  parameter  int unsigned DLY = TCB_HSK_DEF.DLY,
  // TCB widths
  parameter  int unsigned ADR = 32,
  parameter  int unsigned DAT = 32
);

  // TODO: parameter propagation through virtual interfaces in classes
  // is not working well thus this workaround

  // interface configuration
  localparam tcb_cfg_t CFG = TCB_CFG_DEF;
  localparam tcb_vip_t VIP = '{DRV: 1'b1};

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // testbench status signals
  string       testname;  // test name
  int unsigned errorcnt;  // ERROR counter

  // TCB interfaces
  tcb_if #(tcb_cfg_t, CFG, tcb_req_t, tcb_rsp_t, tcb_vip_t, VIP) tcb (.clk (clk), .rst (rst));

  // parameterized class specialization (non-blocking API)
  typedef tcb_vip_blocking_c #(tcb_cfg_t, CFG, tcb_req_t, tcb_rsp_t, tcb_vip_t, VIP) tcb_s;

  // TCB class objects
  tcb_s obj_ref = new(tcb, "MAN");
  tcb_s obj_mon = new(tcb, "MON");
  tcb_s obj_man = new(tcb, "MAN");
  tcb_s obj_sub = new(tcb, "SUB");

////////////////////////////////////////////////////////////////////////////////
// reference data for tests
////////////////////////////////////////////////////////////////////////////////

  // data organized into packed bytes
  typedef logic [tcb.CFG_BUS_BYT-1:0][8-1:0] data_byte_t;

  // created data for tests
  function automatic data_byte_t data_test_f (
    input logic [8/2-1:0] val = 'x
  );
    for (int unsigned i=0; i<tcb.CFG_BUS_BYT; i++) begin
      data_test_f[i] = {val, i[8/2-1:0]};
    end
  endfunction: data_test_f

////////////////////////////////////////////////////////////////////////////////
// test transfer API
////////////////////////////////////////////////////////////////////////////////

  task automatic test_transfer;
    // local variables
    bit lst_wen [2] = '{1'b0, 1'b1};
    int lst_idl [3] = '{0, 1, 2};
    int lst_bpr [3] = '{0, 1, 2};

    tcb_s::transfer_queue_t tst_ref;
    tcb_s::transfer_array_t tst_man;
    tcb_s::transfer_array_t tst_mon;
    tcb_s::transfer_array_t tst_sub;

    int unsigned i;

    testname = "transfer";

    // prepare transactions
    foreach (lst_wen[idx_wen]) begin
      foreach (lst_idl[idx_idl]) begin
        foreach (lst_bpr[idx_bpr]) begin
          tcb_s::transfer_t tst_tmp = '{
            // request
            req: '{
              wen:  lst_wen[idx_wen],
              ren: ~lst_wen[idx_wen],
              ndn: 1'b0,
              adr: 'h00,
              siz: $clog2(tcb.CFG_BUS_BYT),
              ben: '1,
              wdt: data_test_f((8/2)'(2*i+0)),
              default: 'x
            },
            // response
            rsp: '{
              rdt: data_test_f((8/2)'(2*i+1)),
              sts: '0
            },
            // timing
            idl: lst_idl[idx_idl],
            bpr: lst_bpr[idx_bpr],
            // transfer ID
            //id: $sformatf("i=%0d", i)
            id: ""
          };
          tst_ref.push_back(tst_tmp);
          i++;
        end
      end
    end

//    foreach(tst_ref[i]) begin
//      $display("tst_ref[%0d] = %p", i, tst_ref[i]);
//    //$display("tst_ref[%0d] = %0p", i, tst_ref[i]);
//    end

    tst_man = new[tst_ref.size()](tst_ref);
    tst_mon = new[tst_ref.size()];
    tst_sub = new[tst_ref.size()](tst_ref);

    // drive transactions
    $display("INFO: transfer API test begin.");
    fork
      // manager
      begin: fork_man
        obj_man.transfer_sequencer(tst_man);
      end: fork_man
      // monitor
      begin: fork_mon
        obj_mon.transfer_sequencer(tst_mon);
      end: fork_mon
      // subordinate
      begin: fork_sub
        obj_sub.transfer_sequencer(tst_sub);
      end: fork_sub
    join
    $display("INFO: transfer API test end.");

    // check transactions
    $display("INFO: transfer API checks begin.");
    for (int unsigned i=0; i<tst_ref.size(); i++) begin
      // manager
      if (tst_man[i] != tst_ref[i]) begin
        errorcnt++;
        $display("i=%d, REF: %p", i, tst_ref[i]);
        $display("i=%d, MAN: %p", i, tst_man[i]);
      end
      // monitor
      if (tst_mon[i] != tst_ref[i]) begin
        errorcnt++;
        $display("i=%d, REF: %p", i, tst_ref[i]);
        $display("i=%d, MON: %p", i, tst_mon[i]);
      end
      // subordinate
      if (tst_sub[i] != tst_ref[i]) begin
        errorcnt++;
        $display("i=%d, REF: %p", i, tst_ref[i]);
        $display("i=%d, SUB: %p", i, tst_sub[i]);
      end
    end
    $display("INFO: transfer API checks begin.");

  endtask: test_transfer

////////////////////////////////////////////////////////////////////////////////
// test nonblocking API
////////////////////////////////////////////////////////////////////////////////

  task automatic test_nonblocking;
    tcb_s::transfer_queue_t que_ref;
    tcb_s::transfer_queue_t que_mon;
    tcb_s::transfer_queue_t que_man;
    tcb_s::transfer_queue_t que_sub;

    integer unsigned     adr;
    logic                ndn;
    logic [1-1:0][8-1:0] dat8;
    logic [2-1:0][8-1:0] dat16;
    logic [4-1:0][8-1:0] dat32;
    logic [8-1:0][8-1:0] dat64;
    tcb_rsp_sts_t        sts;

    testname = "nonblocking";

    //                 que      adr           ndn         wdt
    obj_ref.put_write8(que_ref, 32'h00000000, TCB_NATIVE, 32'h01, '0);
    obj_ref.put_write8(que_ref, 32'h00000001, TCB_NATIVE, 32'h23, '0);
    obj_ref.put_write8(que_ref, 32'h00000002, TCB_NATIVE, 32'h45, '0);
    obj_ref.put_write8(que_ref, 32'h00000003, TCB_NATIVE, 32'h67, '0);
    //                 que      adr           ndn         rdt
    obj_ref.put_read8 (que_ref, 32'h00000000, TCB_NATIVE, 32'h01, '0);
    obj_ref.put_read8 (que_ref, 32'h00000001, TCB_NATIVE, 32'h23, '0);
    obj_ref.put_read8 (que_ref, 32'h00000002, TCB_NATIVE, 32'h45, '0);
    obj_ref.put_read8 (que_ref, 32'h00000003, TCB_NATIVE, 32'h67, '0);

    //                 que      adr           ndn         wdt
    obj_ref.put_write16(que_ref, 32'h00000010, TCB_NATIVE, 32'h0123, '0);
    obj_ref.put_write16(que_ref, 32'h00000012, TCB_NATIVE, 32'h4567, '0);
    //                 que      adr           ndn         rdt
    obj_ref.put_read16 (que_ref, 32'h00000010, TCB_NATIVE, 32'h0123, '0);
    obj_ref.put_read16 (que_ref, 32'h00000012, TCB_NATIVE, 32'h4567, '0);

    //                 que      adr           ndn         wdt
    obj_ref.put_write32(que_ref, 32'h00000020, TCB_NATIVE, 32'h01234567, '0);
    //                 que      adr           ndn         rdt
    obj_ref.put_read32 (que_ref, 32'h00000020, TCB_NATIVE, 32'h01234567, '0);

    //                 que      adr           ndn         wdt
    obj_ref.put_write64(que_ref, 32'h00000040, TCB_NATIVE, 64'h01234567891abcdef, '0);
    //                 que      adr           ndn         rdt
    obj_ref.put_read64 (que_ref, 32'h00000040, TCB_NATIVE, 54'h01234567891abcdef, '0);

    // copy reference transfer queue
    que_man = que_ref;
    que_sub = que_ref;

    // drive transactions
    $display("INFO: nonblocking API test begin.");
    fork
      // manager
      begin: fork_man
        obj_man.transfer_sequencer(que_man);
      end: fork_man
      // monitor
      begin: fork_mon
        obj_mon.transfer_monitor  (que_mon);
      end: fork_mon
      // subordinate
      begin: fork_sub
        obj_sub.transfer_sequencer(que_sub);
      end: fork_sub
    join_any
    // disable transfer monitor
    repeat(CFG.HSK.DLY) @(posedge clk);
    disable fork;
    $display("INFO: nonblocking API test end.");

    // check transactions
    $display("INFO: nonblocking API checks begin.");
    for (int unsigned i=0; i<que_man.size(); i++) begin
      // manager
      assert (que_mon[i].req ==? que_man[i].req) else $error("\nque_mon[%0d].req = %p !=? \nque_man[%0d].req = %p", i, que_mon[i].req, i, que_man[i].req);
      assert (que_mon[i].rsp ==? que_man[i].rsp) else $error("\nque_mon[%0d].rsp = %p !=? \nque_man[%0d].rsp = %p", i, que_mon[i].rsp, i, que_man[i].rsp);
      // subordinate
      assert (que_mon[i].req ==? que_sub[i].req) else $error("\nque_mon[%0d].req = %p !=? \nque_sub[%0d].req = %p", i, que_mon[i].req, i, que_sub[i].req);
      assert (que_mon[i].rsp ==? que_sub[i].rsp) else $error("\nque_mon[%0d].rsp = %p !=? \nque_sub[%0d].rsp = %p", i, que_mon[i].rsp, i, que_sub[i].rsp);
    end
    $display("INFO: nonblocking API checks begin.");

    foreach(que_man[i])
    $display("DEBUG: que_man[%0d] = %p", i, que_man[i]);

    obj_man.get_write8(que_man, adr, ndn, dat8, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b wdt=8'h%02h sts=%p", adr, ndn, dat8, sts);
    obj_man.get_write8(que_man, adr, ndn, dat8, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b wdt=8'h%02h sts=%p", adr, ndn, dat8, sts);
    obj_man.get_write8(que_man, adr, ndn, dat8, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b wdt=8'h%02h sts=%p", adr, ndn, dat8, sts);
    obj_man.get_write8(que_man, adr, ndn, dat8, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b wdt=8'h%02h sts=%p", adr, ndn, dat8, sts);
    obj_man.get_read8 (que_man, adr, ndn, dat8, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b rdt=8'h%02h sts=%p", adr, ndn, dat8, sts);
    obj_man.get_read8 (que_man, adr, ndn, dat8, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b rdt=8'h%02h sts=%p", adr, ndn, dat8, sts);
    obj_man.get_read8 (que_man, adr, ndn, dat8, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b rdt=8'h%02h sts=%p", adr, ndn, dat8, sts);
    obj_man.get_read8 (que_man, adr, ndn, dat8, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b rdt=8'h%02h sts=%p", adr, ndn, dat8, sts);

    obj_man.get_write16(que_man, adr, ndn, dat16, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b wdt=16'h%04h sts=%p", adr, ndn, dat16, sts);
    obj_man.get_write16(que_man, adr, ndn, dat16, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b wdt=16'h%04h sts=%p", adr, ndn, dat16, sts);
    obj_man.get_read16 (que_man, adr, ndn, dat16, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b rdt=16'h%04h sts=%p", adr, ndn, dat16, sts);
    obj_man.get_read16 (que_man, adr, ndn, dat16, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b rdt=16'h%04h sts=%p", adr, ndn, dat16, sts);

    obj_man.get_write32(que_man, adr, ndn, dat32, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b wdt=32'h%08h sts=%p", adr, ndn, dat32, sts);
    obj_man.get_read32 (que_man, adr, ndn, dat32, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b rdt=32'h%08h sts=%p", adr, ndn, dat32, sts);

    obj_man.get_write64(que_man, adr, ndn, dat64, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b wdt=54'h%016h sts=%p", adr, ndn, dat64, sts);
    obj_man.get_read64 (que_man, adr, ndn, dat64, sts);  $display("DEBUG: adr=32'h%08h ndn=1'b%01b rdt=54'h%016h sts=%p", adr, ndn, dat64, sts);

  endtask: test_nonblocking

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
    
    // tests
//    test_transfer;
    test_nonblocking;

    repeat (2) @(posedge clk);
    if (errorcnt>0)  $display("FAILURE: there were %d errors.", errorcnt);
    else             $display("SUCCESS.");
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_vip_tb
