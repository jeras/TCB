////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library passthrough testbench
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

module tcb_lite_lib_passthrough_tb
    import tcb_lite_pkg::*;
#(
    // RTL configuration parameters
    parameter  int unsigned DLY =    1,  // response delay
    parameter  bit          HLD = 1'b0,  // response hold
    parameter  bit          MOD = 1'b1,  // bus mode (0-logarithmic size, 1-byte enable)
    parameter  int unsigned CTL =    0,  // control width (user defined request signals)
    parameter  int unsigned ADR =   32,  // address width (only 32/64 are supported)
    parameter  int unsigned DAT =   32,  // data    width (only 32/64 are supported)
    parameter  int unsigned STS =    0   // status  width (user defined response signals)
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

    // TCB configurations               '{HSK: '{DLY, HLD}, BUS: '{MOD, CTL, ADR, DAT, STS}}
    localparam tcb_lite_cfg_t MAN_CFG = '{HSK: '{DLY, HLD}, BUS: '{MOD, CTL, ADR, DAT, STS}};
    localparam tcb_lite_cfg_t SUB_CFG = '{HSK: '{DLY, HLD}, BUS: '{MOD, CTL, ADR, DAT, STS}};

    localparam bit VIP = 1'b1;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // system signals (initialized)
    logic clk = 1'b1;  // clock
    logic rst = 1'b1;  // reset

    // TCB interfaces
    tcb_lite_if #(MAN_CFG     ) tcb_man (.clk (clk), .rst (rst));
    tcb_lite_if #(SUB_CFG, VIP) tcb_sub (.clk (clk), .rst (rst));

    // empty array
    logic [8-1:0] nul [];

    // response
    logic [DAT-1:0] rdt;  // read data
    logic [STS-1:0] sts;  // response status
    logic           err;  // response error

    // timing
    int unsigned    idl;  // idle
    int unsigned    bpr;  // backpressure

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

    // clock
    always #(20ns/2) clk = ~clk;

    // test sequence
    initial
    begin: test
        // reset sequence
        repeat (2) @(posedge clk);
        /* verilator lint_off INITIALDLY */
        rst <= 1'b0;
        /* verilator lint_on INITIALDLY */
        repeat (1) @(posedge clk);

        // manager (non-blocking API)

        //                              lck,  ndn,  wen, ctl,          adr,             siz,              byt,          wdt}, idl
        man.req_que.push_back('{req: '{1'b0, 1'b0, 1'b1,  'x, 32'h01234567, tcb_man.SIZ'(2), tcb_man.BYT'('1), 32'h76543210}, idl: 0});
        man.req_que.push_back('{req: '{1'b0, 1'b0, 1'b0,  'x, 32'h89ABCDEF, tcb_man.SIZ'(2), tcb_man.BYT'('1), 32'hxxxxxxxx}, idl: 0});
        //                                      rdt, sts,  err}, bpr
        sub.rsp_que.push_back('{rsp: '{32'hxxxxxxxx,  '0, 1'b0}, bpr: 0});
        sub.rsp_que.push_back('{rsp: '{32'h76543210,  '0, 1'b0}, bpr: 0});

        // wait for queues to get empty
        do begin
            @(posedge clk);
        end while (man.req_que.size() > 0);
        // wait for response delay cycles
        repeat(tcb_man.DLY) @(posedge clk);

        // debug printout
        foreach(    man.rsp_que[i])  $display("DEBUG: man.rsp_que[%0d] = %p", i,     man.rsp_que[i]);
        foreach(    sub.req_que[i])  $display("DEBUG: sub.req_que[%0d] = %p", i,     sub.req_que[i]);
        foreach(mon_man.bus_que[i])  $display("DEBUG: mon_man.que[%0d] = %p", i, mon_man.bus_que[i]);
        foreach(mon_sub.bus_que[i])  $display("DEBUG: mon_sub.que[%0d] = %p", i, mon_sub.bus_que[i]);

//        foreach(man.rsp_que[i]) begin
//            assert (tst_man_mon[i].req ==? tst_ref[i].req) else $error("\ntst_man_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_man_mon[i].req, i, tst_ref[i].req);
//            assert (tst_man_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_man_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_man_mon[i].rsp, i, tst_ref[i].rsp);
//            assert (tst_sub_mon[i].req ==? tst_ref[i].req) else $error("\ntst_sub_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_sub_mon[i].req, i, tst_ref[i].req);
//            assert (tst_sub_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_sub_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_sub_mon[i].rsp, i, tst_ref[i].rsp);
//        end
//
//        // printout transfer queue for debugging purposes
//        foreach (tst_ref[i]) begin
//            $display("DEBUG: tst_ref[%0d] = %p", i, tst_ref[i]);
//        end

        repeat (4) @(posedge clk);
        $finish();
    end: test

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

    // VIP
    tcb_lite_vip_manager              man (.man (tcb_man));
    tcb_lite_vip_subordinate          sub (.sub (tcb_sub));
    tcb_lite_vip_monitor          mon_man (.mon (tcb_man));
    tcb_lite_vip_monitor          mon_sub (.mon (tcb_man));
    tcb_lite_vip_protocol_checker chk_man (.mon (tcb_man));
    tcb_lite_vip_protocol_checker chk_sub (.mon (tcb_sub));

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

    tcb_lite_lib_passthrough dut (
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

endmodule: tcb_lite_lib_passthrough_tb
