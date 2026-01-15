////////////////////////////////////////////////////////////////////////////////
// TCB-Full (Tightly Coupled Bus) library register slice for request path testbench
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

module tcb_full_lib_register_request_tb
    import tcb_full_pkg::*;
    import tcb_full_vip_blocking_pkg::*;
#(
    // TCB widths
    int unsigned ADR = 32,       // address bus width
    int unsigned DAT = 32,       // data    bus width
    // response delay
    int unsigned DLY = 1
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

    localparam tcb_cfg_t CFG_MAN = '{HSK: '{DLY: DLY+1, HLD: 1'b1}, BUS: TCB_BUS_DEF, PMA: TCB_PMA_DEF};
    localparam tcb_cfg_t CFG_SUB = '{HSK: '{DLY: DLY+0, HLD: 1'b1}, BUS: TCB_BUS_DEF, PMA: TCB_PMA_DEF};

    // VIP parameters
    localparam tcb_full_vip_t VIP = '{
        DRV: 1'b1
    };

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // system signals (initialized)
    logic clk = 1'b1;  // clock
    logic rst = 1'b1;  // reset

    // TCB interfaces
    tcb_full_if #(.CFG (CFG_MAN)            ) tcb_man (.clk (clk), .rst (rst));
    tcb_full_if #(.CFG (CFG_SUB), .VIP (VIP)) tcb_sub (.clk (clk), .rst (rst));

    // parameterized class specialization (blocking API)
    typedef tcb_full_vip_blocking_c #(.CFG (CFG_MAN)            ) tcb_man_s;
    typedef tcb_full_vip_blocking_c #(.CFG (CFG_SUB), .VIP (VIP)) tcb_sub_s;

    // TCB class objects
    tcb_man_s obj_man = new(tcb_man, "MAN");
    tcb_sub_s obj_sub = new(tcb_sub, "SUB");

    // transfer reference/monitor array
    tcb_man_s::transfer_queue_t tst_man_mon;
    tcb_sub_s::transfer_queue_t tst_sub_mon;
    tcb_sub_s::transfer_queue_t tst_ref;
    int unsigned                tst_len;

    // empty array
    logic [8-1:0] nul [];

    // response
    logic [tcb_sub.CFG_BUS_BYT-1:0][8-1:0] rdt;  // read data
    tcb_rsp_sts_t                          sts;  // status response

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
        rst <= 1'b0;
        repeat (1) @(posedge clk);

        fork
            // manager (blocking API)
            begin: fork_man
                obj_man.write32(32'h01234567, 32'h76543210, sts);
                obj_man.read32 (32'h89ABCDEF, rdt         , sts);
            end: fork_man
            // subordinate (monitor)
            begin: fork_man_monitor
                obj_man.transfer_monitor(tst_man_mon);
            end: fork_man_monitor
            begin: fork_sub
                // subordinate transfer queue
                sts = '0;
                tst_ref.delete();
                tst_len = tst_ref.size();
                tst_len += {obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h01234567, wdt: '{8'h10, 8'h32, 8'h54, 8'h76}, default: 'x}, rsp: '{rdt: nul, sts: sts}})};
                tst_len += {obj_sub.put_transaction(tst_ref, '{req: '{adr: 32'h89ABCDEF, wdt: nul, default: 'x}, rsp: '{rdt: '{8'h98, 8'hBA, 8'hDC, 8'hFE}, sts: sts}})};
                obj_sub.transfer_sequencer(tst_ref);
            end: fork_sub
            // subordinate (monitor)
            begin: fork_sub_monitor
                obj_sub.transfer_monitor(tst_sub_mon);
            end: fork_sub_monitor
        join_any
        // disable transfer monitor
        repeat (tcb_man.CFG.HSK.DLY) @(posedge clk);
        disable fork;

        foreach(tst_ref[i]) begin
            assert (tst_man_mon[i].req ==? tst_ref[i].req) else $error("\ntst_man_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_man_mon[i].req, i, tst_ref[i].req);
            assert (tst_man_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_man_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_man_mon[i].rsp, i, tst_ref[i].rsp);
            assert (tst_sub_mon[i].req ==? tst_ref[i].req) else $error("\ntst_sub_mon[%0d].req = %p !=? \ntst_ref[%0d].req = %p", i, tst_sub_mon[i].req, i, tst_ref[i].req);
            assert (tst_sub_mon[i].rsp ==? tst_ref[i].rsp) else $error("\ntst_sub_mon[%0d].rsp = %p !=? \ntst_ref[%0d].rsp = %p", i, tst_sub_mon[i].rsp, i, tst_ref[i].rsp);
        end

        // printout transfer queue for debugging purposes
        foreach (tst_ref[i]) begin
            $display("DEBUG: tst_ref[%0d] = %p", i, tst_ref[i]);
        end

        repeat (4) @(posedge clk);
        $finish();
    end: test

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

    tcb_full_vip_protocol_checker chk_man (
        .tcb (tcb_man)
    );

    tcb_full_vip_protocol_checker chk_sub (
        .tcb (tcb_sub)
    );

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

    tcb_full_lib_register_request dut (
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

endmodule: tcb_full_lib_register_request_tb
