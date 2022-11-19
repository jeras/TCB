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
  int unsigned DLY = 0
);

////////////////////////////////////////////////////////////////////////////////
// local functions
////////////////////////////////////////////////////////////////////////////////

  typedef logic [BEW-1:0][SLW-1:0] data_t;

  function automatic data_t data_f (
    input logic [SLW/2-1:0] val = 'x
  );
    for (int unsigned i=0; i<BEW; i++) begin
      data_f[i] = {val, i[SLW/2-1:0]};
    end
  endfunction: data_f;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // physical layer data
  int unsigned    len = BEW;
  dat_t           dat;

  // supported data widths
  data8_t         data8;
  data16_t        data16;
  data32_t        data32;
  data64_t        data64;
  data128_t       data128;
  // native data width
  data_t          data;

  // temporary variables
  logic [BEW-1:0] ben;  // byte enable
  logic [DBW-1:0] rdt;  // read data
  logic           err;  // error response
  // timing idle/backpressure
  int unsigned    idl;
  int unsigned    bpr;

  // TCB interface
  tcb_if #(.ABW (ABW), .DBW (DBW), .SLW (SLW), .DLY (DLY)) tcb (.clk (clk), .rst (rst));

  // ERROR counter
  int unsigned error;

////////////////////////////////////////////////////////////////////////////////
// test low level req/rsp tasks
////////////////////////////////////////////////////////////////////////////////

  // request structure
  typedef struct {
    // request optional
    logic                            rpt;  // repeat access
    logic                            lck;  // arbitration lock
    // request
    logic                            wen;  // write enable
    logic              [tcb.ABW-1:0] adr;  // address
    logic              [tcb.BEW-1:0] ben;  // byte enable
    logic [tcb.BEW-1:0][tcb.SLW-1:0] wdt;  // write data
    // response
    logic [tcb.BEW-1:0][tcb.SLW-1:0] rdt;  // read data
    logic                            err;  // error
    // timing idle/backpressure
    int unsigned                     idl;  // idle
    int unsigned                     bpr;  // backpressure
  } tcb_t;

  task automatic test_req_rsp;
    // local variables
    bit lst_wen [2] = '{1'b0, 1'b1};

    int unsigned tst_num = 2;

    tcb_t        tst_ref [$size(lst_wen)];
    tcb_t        tst_tmp [$size(lst_wen)];

    // prepare transactions
    foreach (lst_wen[idx_wen]) begin
      $display("lst_wen[idx_wen=%d] = %b", idx_wen, lst_wen[idx_wen]);
      tst_ref[idx_wen] = '{
        rpt: 1'b0,
        lck: 1'b0,
        wen: lst_wen[idx_wen],
        adr: 'h00,
        ben: '1,
        wdt: data_f((SLW/2)'(2*idx_wen+0)),
        rdt: data_f((SLW/2)'(2*idx_wen+1)),
        err: 1'b0,
        idl: 0,
        bpr: 0
      };
    end

    // drive transactions
    fork
      begin: man_req
        for (int unsigned i=0; i<tst_num; i++) begin
          man.req(
            .rpt  (tst_ref[i].rpt),
            .lck  (tst_ref[i].lck),
            .wen  (tst_ref[i].wen),
            .adr  (tst_ref[i].adr),
            .ben  (tst_ref[i].ben),
            .wdt  (tst_ref[i].wdt),
            .idl  (tst_ref[i].idl),
            .bpr  (tst_tmp[i].bpr)
          );
        end
      end: man_req
      begin: man_rsp
        for (int unsigned i=0; i<tst_num; i++) begin
          man.rsp(
            .rdt  (tst_tmp[i].rdt),
            .err  (tst_tmp[i].err)
          );
        end
      end: man_rsp
      begin: sub_req_rsp
        for (int unsigned i=0; i<tst_num; i++) begin
          sub.req_rsp(
            .rpt  (tst_tmp[i].rpt),
            .lck  (tst_tmp[i].lck),
            .wen  (tst_tmp[i].wen),
            .adr  (tst_tmp[i].adr),
            .ben  (tst_tmp[i].ben),
            .wdt  (tst_tmp[i].wdt),
            .rdt  (tst_ref[i].rdt),
            .err  (tst_ref[i].err),
            .idl  (tst_tmp[i].idl),
            .bpr  (tst_tmp[i].bpr)
          );
        end
      end: sub_req_rsp
    join

    // check transactions
    for (int unsigned i=0; i<tst_num; i++) begin
      if (tst_tmp[i] != tst_ref[i]) begin
        error++;
        $display("i=%d, REF: %p", i, tst_ref[i]);
        $display("i=%d, TMP: %p", i, tst_tmp[i]);
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