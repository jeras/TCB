////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verifivation IP) manager/monitor/subordinate TestBench
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
  import tcb_vip_pkg::*;
#(
  // TCB widths
  int unsigned ABW = 32,       // address bus width
  int unsigned DBW = 32,       // data    bus width
  int unsigned SLW =       8,  // selection   width
  int unsigned BEW = DBW/SLW,  // byte enable width
  // response delay
  int unsigned DLY = 1
);

  // parameterized class specialization
  typedef tcb_c #(tcb.ABW, tcb.DBW, tcb.SLW) tcb_s;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // TCB interface
  tcb_if #(.ABW (ABW), .DBW (DBW), .SLW (SLW), .DLY (DLY)) tcb (.clk (clk), .rst (rst));

  // ERROR counter
  int unsigned error;

////////////////////////////////////////////////////////////////////////////////
// test low level req/rsp tasks
////////////////////////////////////////////////////////////////////////////////

  task automatic test_req_rsp;
    // local variables
    bit lst_wen [2] = '{1'b0, 1'b1};
    int lst_idl [3] = '{0, 1, 2};
    int lst_bpr [3] = '{0, 1, 2};

    int unsigned tst_num = $size(lst_wen) * $size(lst_idl) * $size(lst_bpr);

    tcb_s::transaction_t tst_ref [] = new[tst_num];
    tcb_s::transaction_t tst_man [];
    tcb_s::transaction_t tst_sub [];

    // prepare transactions
    int unsigned i;
    foreach (lst_wen[idx_wen]) begin
      foreach (lst_idl[idx_idl]) begin
        foreach (lst_bpr[idx_bpr]) begin
          tst_ref[i] = '{
            rpt: 1'b0,
            lck: 1'b0,
            wen: lst_wen[idx_wen],
            adr: 'h00,
            ben: '1,
            wdt: tcb_s::data_test_f((SLW/2)'(2*i+0)),
            rdt: tcb_s::data_test_f((SLW/2)'(2*i+1)),
            err: 1'b0,
            idl: lst_idl[idx_idl],
            bpr: lst_bpr[idx_bpr]
          };
          i++;
        end
      end
    end

    tst_man = new[tst_ref.size()](tst_ref);
    tst_sub = new[tst_ref.size()](tst_ref);

    // DEBUG printout
//    $display("REF: %p", tst_ref);
//    $display("MAN: %p", tst_man);
//    $display("SUB: %p", tst_sub);

    // drive transactions
    fork
      begin: fork_man
        man.sequencer(tst_man);
        $display("DEBUG: END of manager");
      end: fork_man
      begin: fork_sub
        sub.sequencer(tst_sub);
        $display("DEBUG: END of subordinate");
      end: fork_sub
    join

    // check transactions
    for (int unsigned i=0; i<tst_num; i++) begin
//      $display("i=%d, REF: %p", i, tst_ref[i]);
      if (tst_man[i] != tst_ref[i]) begin
        error++;
        $display("i=%d, MAN: %p", i, tst_man[i]);
      end
      if (tst_sub[i] != tst_ref[i]) begin
        error++;
        $display("i=%d, REF: %p", i, tst_ref[i]);
        $display("i=%d, SUB: %p", i, tst_sub[i]);
      end
    end

  endtask: test_req_rsp


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
    #1;
    rst = 1'b0;
    repeat (1) @(posedge clk);
    
    // test low level req/rsp tests
    test_req_rsp;

//    // test low level transaction tasks
//    len = BEW;
//    // prepare data
//    dat = dat_f(4, 1);
//    data = data_f(2);
//    // transaction
//    idl = 0;
//    fork
//      begin: req_transaction
//        man.transaction(1'b0, 1'b0, len, 1'b1, 16, dat, err, idl, bpr);
//      end: req_transaction
//      begin: rsp_transaction
//        sub.rsp(data, 1'b0);
//      end: rsp_transaction
//    join
//    // check data
//    if (dat != dat_f(4, 2)) error++;
//
//    // test BFM read/write tasks
//    fork
//      begin: req_rw
//        //         adr,     ben,          wdt, err, lck, rpt
//        man.write('h00, 4'b1111, 32'h01234567, err);
//        man.read ('h00, 4'b1111, rdt         , err);
//        man.write('h00, 4'b1111, 32'h01234567, err);
//        man.read ('h00, 4'b1111, rdt         , err);
//      end: req_rw
//      begin: rsp_rw
//        //               rdt,  err, tmg
//        sub.rsp(32'h55xxxxxx, 1'b0);
//        sub.rsp(32'h76543210, 1'b0);
//        sub.rsp(32'h55xxxxxx, 1'b0, 1);
//        sub.rsp(32'h76543210, 1'b0, 1);
//      end: rsp_rw
//    join

    repeat (2) @(posedge clk);
    if (error>0)  $display("FAILURE: there were %d errors.", error);
    else          $display("SUCCESS.");
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  // manager
  tcb_vip_man man (.tcb (tcb));

  // monitor
  tcb_vip_mon mon (.tcb (tcb));

  // subordinate
  tcb_vip_sub sub (.tcb (tcb));

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
  //$dumpfile("test.vcd");
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_vip_tb