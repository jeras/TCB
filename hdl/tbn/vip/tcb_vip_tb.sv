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
  int unsigned ADR = 32,
  int unsigned DAT = 32,
  // response delay
  int unsigned DLY = 0,
  // memory port number
  int unsigned PN = 1
);

  // TODO: parameter propagation through virtual interfaces in classes
  // is not working well thus this workaround

  // physical interface parameter
  localparam tcb_par_phy_t PHY1 = '{
    // protocol
    DLY: DLY,
    // signal bus widths
    SLW: TCB_PAR_PHY_DEF.SLW,
    ADR: ADR,
    DAT: DAT,
    ALW: $clog2(DAT/TCB_PAR_PHY_DEF.SLW),
    // size/mode/order parameters
    SIZ: TCB_PAR_PHY_DEF.SIZ,
    MOD: TCB_PAR_PHY_DEF.MOD,
    ORD: TCB_PAR_PHY_DEF.ORD,
    // channel configuration
    CHN: TCB_PAR_PHY_DEF.CHN
  };

  localparam tcb_par_phy_t PHY = TCB_PAR_PHY_DEF;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals
  logic clk;  // clock
  logic rst;  // reset
/*
  // TCB interfaces
  tcb_if #(.PHY (PHY)) tcb              (.clk (clk), .rst (rst));
  tcb_if #(.PHY (PHY)) tcb_mem [0:PN-1] (.clk (clk), .rst (rst));
*/
  // TCB interfaces
  tcb_if tcb              (.clk (clk), .rst (rst));
  tcb_if tcb_mem [0:PN-1] (.clk (clk), .rst (rst));

  // parameterized class specialization
  typedef tcb_transfer_c #(.PHY (PHY)) tcb_s;

  // TCB class objects
  tcb_s obj_man;
  tcb_s obj_mon;
  tcb_s obj_sub;
  tcb_s obj_mem [0:PN-1];

  // testbench status signals
  string       testname;  // test name
  int unsigned errorcnt;  // ERROR counter

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
            // request
            req: '{
              cmd: '0,
              wen: lst_wen[idx_wen],
              ndn: 1'b0,
              adr: 'h00,
              siz: $clog2(tcb.PHY_BEN),
              ben: '1,
              wdt: tcb_s::data_test_f((tcb.PHY.SLW/2)'(2*i+0))
            },
            // response
            rsp: '{
              rdt: tcb_s::data_test_f((tcb.PHY.SLW/2)'(2*i+1)),
              sts: '0
            },
            // timing
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
    for (int unsigned i=0; i<tst_num; i++) begin
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

  endtask: test_nonblocking

////////////////////////////////////////////////////////////////////////////////
// test blocking API
////////////////////////////////////////////////////////////////////////////////

  // response
  logic [PHY.DAT-1:0] rdt;  // read data
  tcb_rsp_sts_def_t   sts;  // status response

  logic [  8-1:0] rdt8  ;  //   8-bit read data
  logic [ 16-1:0] rdt16 ;  //  16-bit read data
  logic [ 32-1:0] rdt32 ;  //  32-bit read data
  logic [ 64-1:0] dat64 ;  //  64-bit read data
  logic [128-1:0] dat128;  // 128-bit read data

  task automatic test_blocking;
    $display("INFO: blocking API test begin.");
    //                adr,          dat, sts
    obj_mem[0].write32('h00, 32'h01234567, sts);
    obj_mem[0].read32 ('h00, rdt32       , sts);
    //                adr,          dat, sts
    obj_mem[0].write32('h11, 32'h01234567, sts);
    obj_mem[0].read32 ('h11, rdt32       , sts);
    $display("INFO: blocking API test begin.");
  endtask: test_blocking

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  initial          clk = 1'b1;
  always #(20ns/2) clk = ~clk;

  generate
  for (genvar i=0; i<PN; i++) begin
    initial begin
      obj_mem[i] = new("MAN", tcb_mem[i]);
    end
  end
  endgenerate

  // test sequence
  initial
  begin
    // connect virtual interfaces
    obj_man = new("MAN", tcb);
    obj_mon = new("MON", tcb);
    obj_sub = new("SUB", tcb);
    // reset sequence
    rst = 1'b1;
    repeat (2) @(posedge clk);
    rst = 1'b0;
    repeat (1) @(posedge clk);
    
    // test non blobking API
    testname = "nonblocking";
    test_nonblocking;
    repeat (2) @(posedge clk);
    // test blobking API
    testname = "blocking";
    test_blocking;
    repeat (2) @(posedge clk);

    if (errorcnt>0)  $display("FAILURE: there were %d errorcnts.", errorcnt);
    else          $display("SUCCESS.");
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  // memory model subordinate
  tcb_vip_memory         mem       (.tcb (tcb_mem));

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_vip_tb
