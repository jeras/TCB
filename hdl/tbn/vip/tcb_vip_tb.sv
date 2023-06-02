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
  import tcb_vip_pkg::*;
#(
  // TCB widths
  tcb_par_phy_t PHY = '{ABW: 32, DBW: 32, SLW: 8},
  //tcb_par_log_t LOG = '{},
  // response delay
  int unsigned DLY = 0,
  // memory port number
  int unsigned PN = 1
);

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // TCB interface
  tcb_if #(.PHY (PHY), .DLY (DLY)) tcb          (.clk (clk), .rst (rst));
  tcb_if #(.PHY (PHY), .DLY (DLY)) bus [0:PN-1] (.clk (clk), .rst (rst));

  // ERROR counter
  int unsigned error;

  // parameterized class specialization
  typedef tcb_transfer_c #(PHY) tcb_s;

////////////////////////////////////////////////////////////////////////////////
// test non-blocking API
////////////////////////////////////////////////////////////////////////////////

  task automatic test_nonblocking;
    // local variables
    bit lst_wen [2] = '{1'b0, 1'b1};
    int lst_idl [3] = '{0, 1, 2};
    int lst_bpr [3] = '{0, 1, 2};

    int unsigned tst_num = $size(lst_wen) * $size(lst_idl) * $size(lst_bpr);

    tcb_s::transfer_array_t tst_ref = new[tst_num];
    tcb_s::transfer_array_t tst_man;
    tcb_s::transfer_array_t tst_mon;
    tcb_s::transfer_array_t tst_sub;

    // prepare transactions
    int unsigned i;
    foreach (lst_wen[idx_wen]) begin
      foreach (lst_idl[idx_idl]) begin
        foreach (lst_bpr[idx_bpr]) begin
          tst_ref[i] = '{
            req: '{
              // request optional
              inc: 1'b0,
              rpt: 1'b0,
              lck: 1'b0,
              ndn: 1'b0,
              // request
              wen: lst_wen[idx_wen],
              adr: 'h00,
              siz: $clog2(tcb.PHY_BEW),
              ben: '1,
              wdt: tcb_s::data_test_f((tcb.PHY.SLW/2)'(2*i+0))
            },
            rsp: '{
              // response
              rdt: tcb_s::data_test_f((tcb.PHY.SLW/2)'(2*i+1)),
              err: 1'b0
            },
            idl: lst_idl[idx_idl],
            bpr: lst_bpr[idx_bpr]
          };
          i++;
        end
      end
    end

    tst_man = new[tst_ref.size()](tst_ref);
    tst_mon = new[tst_ref.size()](tst_ref);
    tst_sub = new[tst_ref.size()](tst_ref);

    // drive transactions
    fork
      // manager
      begin: fork_man
        man.transfer_sequencer(tst_man);
      end: fork_man
      // monitor
      begin: fork_mon
        mon.transfer_sequencer(tst_mon);
      end: fork_mon
      // subordinate
      begin: fork_sub
        sub.transfer_sequencer(tst_sub);
      end: fork_sub
    join

    // check transactions
    for (int unsigned i=0; i<tst_num; i++) begin
      // manager
      if (tst_man[i] != tst_ref[i]) begin
        error++;
        $display("i=%d, REF: %p", i, tst_ref[i]);
        $display("i=%d, MAN: %p", i, tst_man[i]);
      end
      // monitor
      if (tst_mon[i] != tst_ref[i]) begin
        error++;
        $display("i=%d, REF: %p", i, tst_ref[i]);
        $display("i=%d, MON: %p", i, tst_mon[i]);
      end
      // subordinate
      if (tst_sub[i] != tst_ref[i]) begin
        error++;
        $display("i=%d, REF: %p", i, tst_ref[i]);
        $display("i=%d, SUB: %p", i, tst_sub[i]);
      end
    end

  endtask: test_nonblocking

////////////////////////////////////////////////////////////////////////////////
// test blocking API
////////////////////////////////////////////////////////////////////////////////

  logic [  8-1:0] dat8;
  logic [ 16-1:0] dat16;
  logic [ 32-1:0] dat32;
  logic [ 64-1:0] dat64;
  logic [128-1:0] dat128;

  logic [tcb.PHY_DBW-1:0] dat;
  logic                   err;

  task automatic test_blocking;
    //            adr,          dat, err
    cpu[0].write('h00, 32'h01234567, err);
    cpu[0].read ('h00, dat         , err);
    
    cpu[0].write('h11, 32'h01234567, err);
    cpu[0].read ('h11, dat         , err);
  endtask: test_blocking

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
    
    // test non_blobking API
    test_nonblocking;
//    repeat (2) @(posedge clk);
//    test_blocking;

    repeat (2) @(posedge clk);
    if (error>0)  $display("FAILURE: there were %d errors.", error);
    else          $display("SUCCESS.");
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  tcb_vip_dev #("MAN") man          (.tcb (tcb));  // manager
  tcb_vip_dev #("MON") mon          (.tcb (tcb));  // monitor
  tcb_vip_dev #("SUB") sub          (.tcb (tcb));  // subordinate

  tcb_vip_dev #("MAN") cpu [0:PN-1] (.tcb (bus));  // CPU model
  tcb_vip_mem          mem          (.tcb (bus));  // memory

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_vip_tb
