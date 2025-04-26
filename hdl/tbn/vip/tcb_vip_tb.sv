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
  parameter  int unsigned PHY_DLY = 1,
  // TCB widths
  parameter  int unsigned PHY_ADR = 32,
  parameter  int unsigned PHY_DAT = 32,
  // memory interface number
  parameter  int unsigned IFN = 1
);

  // TODO: parameter propagation through virtual interfaces in classes
  // is not working well thus this workaround

  // physical interface parameter
  localparam tcb_phy_t PHY = '{
    // protocol
    DLY: PHY_DLY,
    // signal bus widths
    UNT: TCB_PAR_PHY_DEF.UNT,
    ADR: PHY_ADR,
    DAT: PHY_DAT,
    // size/mode/order parameters
    ALN: $clog2(PHY_DAT/TCB_PAR_PHY_DEF.UNT),
    MIN: TCB_PAR_PHY_DEF.MIN,
    OFF: TCB_PAR_PHY_DEF.OFF,
    MOD: TCB_PAR_PHY_DEF.MOD,
    ORD: TCB_PAR_PHY_DEF.ORD,
    // channel configuration
    CHN: TCB_PAR_PHY_DEF.CHN
  };

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // testbench status signals
  string       testname;  // test name
  int unsigned errorcnt;  // ERROR counter

////////////////////////////////////////////////////////////////////////////////
// reference data for tests
////////////////////////////////////////////////////////////////////////////////

  // data organized into packed bytes
  typedef logic [tcb.PHY_BEN-1:0][tcb.PHY.UNT-1:0] data_byte_t;

  // created data for tests
  function automatic data_byte_t data_test_f (
    input logic [tcb.PHY.UNT/2-1:0] val = 'x
  );
    for (int unsigned i=0; i<tcb.PHY_BEN; i++) begin
      data_test_f[i] = {val, i[tcb.PHY.UNT/2-1:0]};
    end
  endfunction: data_test_f

////////////////////////////////////////////////////////////////////////////////
// test non-blocking API
////////////////////////////////////////////////////////////////////////////////

  // transaction counter
  int unsigned tcb_cnt;

  // TCB interfaces
  tcb_if #(.PHY (PHY)) tcb (.clk (clk), .rst (rst));

  // parameterized class specialization (non-blocking API)
  typedef tcb_vip_transfer_c #(.PHY (PHY)) tcb_nba_s;

  // TCB class objects
  tcb_nba_s obj_man;
  tcb_nba_s obj_mon;
  tcb_nba_s obj_sub;

  task automatic test_nonblocking;
    // local variables
    bit lst_wen [2] = '{1'b0, 1'b1};
    int lst_idl [3] = '{0, 1, 2};
    int lst_bpr [3] = '{0, 1, 2};

    tcb_nba_s::transfer_t       tst_ref [$];
    tcb_nba_s::transfer_array_t tst_man;
    tcb_nba_s::transfer_array_t tst_mon;
    tcb_nba_s::transfer_array_t tst_sub;

    // prepare transactions
    int unsigned i;
    foreach (lst_wen[idx_wen]) begin
      foreach (lst_idl[idx_idl]) begin
        foreach (lst_bpr[idx_bpr]) begin
          tcb_nba_s::transfer_t tst_tmp = '{
            // request
            req: '{
              cmd: '0,
              wen: lst_wen[idx_wen],
              ndn: 1'b0,
              adr: 'h00,
              siz: $clog2(tcb.PHY_BEN),
              ben: '1,
              wdt: data_test_f((tcb.PHY.UNT/2)'(2*i+0))
            },
            // response
            rsp: '{
              rdt: data_test_f((tcb.PHY.UNT/2)'(2*i+1)),
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
// test blocking API
////////////////////////////////////////////////////////////////////////////////

  // TCB interfaces
  tcb_if #(.PHY (PHY)) tcb_mem [0:IFN-1] (.clk (clk), .rst (rst));

  // parameterized class specialization (blocking API)
  typedef tcb_vip_blocking_c #(.PHY (PHY)) tcb_bla_s;

  // TCB class objects
  tcb_bla_s obj_mem [0:IFN-1];

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
    $display("INFO: blocking API test end.");
  endtask: test_blocking

  generate
    for (genvar i=0; i<IFN; i++) begin
      initial begin
        obj_mem[i] = new("MAN", tcb_mem[i]);
      end
    end
  endgenerate
  
////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  initial          clk = 1'b1;
  always #(20ns/2) clk = ~clk;

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
//    // test blobking API
//    testname = "blocking";
//    test_blocking;
//    repeat (2) @(posedge clk);

    if (errorcnt>0)  $display("FAILURE: there were %d errorcnts.", errorcnt);
    else             $display("SUCCESS.");
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  // memory model subordinate
  tcb_vip_memory #(
    .SIZ (2**8)
  ) mem (
    .tcb (tcb_mem)
  );

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
