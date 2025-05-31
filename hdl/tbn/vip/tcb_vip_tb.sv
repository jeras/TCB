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
  import tcb_vip_blocking_pkg::*;
#(
  // response delay
  parameter  int unsigned HSK.DLY = TCB_HSK_DEF,
  // TCB widths
  parameter  int unsigned BUS_ADR = 32,
  parameter  int unsigned BUS_DAT = 32
);

  // TODO: parameter propagation through virtual interfaces in classes
  // is not working well thus this workaround

  // physical interface parameter
  localparam tcb_bus_t BUS = TCB_BUS_DEF;
  localparam tcb_pma_t PMA = TCB_PMA_DEF;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // testbench status signals
  string       testname;  // test name
  int unsigned errorcnt;  // ERROR counter

  localparam bit VIP = 1'b1;

////////////////////////////////////////////////////////////////////////////////
// reference data for tests
////////////////////////////////////////////////////////////////////////////////

  // data organized into packed bytes
  typedef logic [tcb.BUS_BEN-1:0][8-1:0] data_byte_t;

  // created data for tests
  function automatic data_byte_t data_test_f (
    input logic [8/2-1:0] val = 'x
  );
    for (int unsigned i=0; i<tcb.BUS_BEN; i++) begin
      data_test_f[i] = {val, i[8/2-1:0]};
    end
  endfunction: data_test_f

////////////////////////////////////////////////////////////////////////////////
// test non-blocking API
////////////////////////////////////////////////////////////////////////////////

  // transaction counter
  int unsigned tcb_cnt;

  // TCB interfaces
  tcb_if #(HSK.DLY, tcb_bus_t, BUS, tcb_pma_t, PMA, tcb_req_t, tcb_rsp_t, VIP) tcb (.clk (clk), .rst (rst));

  // parameterized class specialization (non-blocking API)
  typedef tcb_vip_transfer_c #(HSK.DLY, tcb_bus_t, BUS, tcb_pma_t, PMA, tcb_req_t, tcb_rsp_t, VIP) tcb_transfer_s;

  // TCB class objects
  tcb_transfer_s obj_man = new(tcb, "MAN");
  tcb_transfer_s obj_mon = new(tcb, "MON");
  tcb_transfer_s obj_sub = new(tcb, "SUB");

  task automatic test_nonblocking;
    // local variables
    bit lst_wen [2] = '{1'b0, 1'b1};
    int lst_idl [3] = '{0, 1, 2};
    int lst_bpr [3] = '{0, 1, 2};

    tcb_transfer_s::transfer_queue_t tst_ref;
    tcb_transfer_s::transfer_array_t tst_man;
    tcb_transfer_s::transfer_array_t tst_mon;
    tcb_transfer_s::transfer_array_t tst_sub;

    // prepare transactions
    int unsigned i;
    foreach (lst_wen[idx_wen]) begin
      foreach (lst_idl[idx_idl]) begin
        foreach (lst_bpr[idx_bpr]) begin
          tcb_transfer_s::transfer_t tst_tmp = '{
            // request
            req: '{
              cmd: '0,
              wen:  lst_wen[idx_wen],
              ren: ~lst_wen[idx_wen],
              ndn: 1'b0,
              adr: 'h00,
              siz: $clog2(tcb.BUS_BEN),
              ben: '1,
              wdt: data_test_f((8/2)'(2*i+0))
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
    $display("INFO: non blocking API test begin.");
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
    $display("INFO: non blocking API test end.");

    // check transactions
    $display("INFO: non blocking API checks begin.");
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
    $display("INFO: non blocking API checks begin.");

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
    
    // test non blocking API
    testname = "nonblocking";
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
