////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library register slice for backpressure path testbench
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

module tcb_lite_lib_register_backpressure_tb
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

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // system signals (initialized)
    logic clk = 1'b1;  // clock
    logic rst = 1'b1;  // reset

    // TCB interfaces
    tcb_lite_if #(MAN_CFG) tcb_man (.clk (clk), .rst (rst));
    tcb_lite_if #(SUB_CFG) tcb_sub (.clk (clk), .rst (rst));

    // empty array
    logic [8-1:0] nul [];

    // response
    logic [DAT-1:0] rdt;  // read data
    logic [STS-1:0] sts;  // response status
    logic           err;  // response error

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

//        fork
//            // manager (blocking API)
//            begin: fork_man
//                obj_man.write32(32'h01234567, 32'h76543210, sts);
//                obj_man.read32 (32'h89ABCDEF, rdt         , sts);
//            end: fork_man
//            // subordinate (monitor)
//            begin: fork_man_monitor
//                obj_man.transfer_monitor(tst_man_mon);
//            end: fork_man_monitor
//            begin: fork_sub
//                // subordinate transfer queue
//                sts = '0;
//                tst_ref.delete();
//                tst_len = tst_ref.size();
//                tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h01234567, wdt: '{8'h10, 8'h32, 8'h54, 8'h76}, default: 'x}, rsp: '{rdt: nul, sts: sts}});
//                tst_len += obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h89ABCDEF, wdt: nul, default: 'x}, rsp: '{rdt: '{8'h98, 8'hBA, 8'hDC, 8'hFE}, sts: sts}});
//                obj_sub.transfer_sequencer(tst_ref);
//            end: fork_sub
//            // subordinate (monitor)
//            begin: fork_sub_monitor
//                obj_sub.transfer_monitor(tst_sub_mon);
//            end: fork_sub_monitor
//        join_any
//        // disable transfer monitor
//        repeat (tcb_man.CFG.HSK.DLY) @(posedge clk);
//        disable fork;
//
//        foreach(tst_ref[i]) begin
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

    // manager VIP
    tcb_lite_vip_manager #(
    ) man (
        .man (tcb_man)
    );

    // subordinate VIP
    tcb_lite_vip_subordinate #(
    ) sub (
        .sub (tcb_sub)
    );

    // manager TCB-Lite protocol checker
    tcb_lite_vip_protocol_checker chk_man (
        .mon (tcb_man)
    );

    // subordinate TCB-Lite protocol checker
    tcb_lite_vip_protocol_checker chk_sub (
        .mon (tcb_sub)
    );

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

    tcb_lite_lib_register_backpressure dut (
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

endmodule: tcb_lite_lib_register_backpressure_tb
