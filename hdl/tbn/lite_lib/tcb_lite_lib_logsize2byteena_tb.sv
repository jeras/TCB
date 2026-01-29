////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library logsize2byteena testbench
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

module tcb_lite_lib_logsize2byteena_tb
    import tcb_lite_pkg::*;
#(
    // RTL configuration parameters
    parameter  int unsigned DLY =    0,  // response delay
    parameter  bit          HLD = 1'b0,  // response hold
    parameter  bit          MOD = 1'b0,  // bus mode (0-logarithmic size, 1-byte enable)
    parameter  int unsigned CTL =    0,  // control width (user defined request signals)
    parameter  int unsigned ADR =   32,  // address width (only 32/64 are supported)
    parameter  int unsigned DAT =   32,  // data    width (only 32/64 are supported)
    parameter  int unsigned STS =    0,  // status  width (user defined response signals)
    // DUT specific parameters
    parameter  bit ALIGNED = 1'b0
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

    // TCB configurations               '{HSK: '{DLY, HLD}, BUS: '{ MOD, CTL, ADR, DAT, STS}}
    localparam tcb_lite_cfg_t MAN_CFG = '{HSK: '{DLY, HLD}, BUS: '{1'b0, CTL, ADR, DAT, STS}};
    localparam tcb_lite_cfg_t SUB_CFG = '{HSK: '{DLY, HLD}, BUS: '{1'b1, CTL, ADR, DAT, STS}};

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // system signals (initialized)
    logic clk = 1'b1;  // clock
    logic rst = 1'b1;  // reset

    string testname = "none";

    // TCB interfaces
    tcb_lite_if #(MAN_CFG) tcb_man       (.clk (clk), .rst (rst));
    tcb_lite_if #(SUB_CFG) tcb_sub       (.clk (clk), .rst (rst));
    tcb_lite_if #(SUB_CFG) tcb_mem [0:0] (.clk (clk), .rst (rst));

    // empty array
    logic [8-1:0] nul [];

    // response
    logic [DAT-1:0] rdt;  // read data
    logic [STS-1:0] sts;  // response status
    logic           err;  // response error

////////////////////////////////////////////////////////////////////////////////
// tests
////////////////////////////////////////////////////////////////////////////////

    task test_aligned ();
        testname = "aligned";
        $display("TEST: %s", testname);

            man.rsp_que.delete();
        mon_man.bus_que.delete();
        mon_sub.bus_que.delete();

        // aligned write
        man.write8 (32'h00000010,        8'h10, sts, err);
        man.write8 (32'h00000011,      8'h32  , sts, err);
        man.write8 (32'h00000012,    8'h54    , sts, err);
        man.write8 (32'h00000013,  8'h76      , sts, err);
        man.write16(32'h00000020,     16'h3210, sts, err);
        man.write16(32'h00000022, 16'h7654    , sts, err);
        man.write32(32'h00000030, 32'h76543210, sts, err);
        @(posedge clk)
        // aligned read
        man.read8 (32'h00000010, rdt[0+:8 ], sts, err);  assert (rdt[0+:8 ] ==         8'h10) else $error("read data mismatch");
        man.read8 (32'h00000011, rdt[0+:8 ], sts, err);  assert (rdt[0+:8 ] ==       8'h32  ) else $error("read data mismatch");
        man.read8 (32'h00000012, rdt[0+:8 ], sts, err);  assert (rdt[0+:8 ] ==     8'h54    ) else $error("read data mismatch");
        man.read8 (32'h00000013, rdt[0+:8 ], sts, err);  assert (rdt[0+:8 ] ==   8'h76      ) else $error("read data mismatch");
        man.read16(32'h00000020, rdt[0+:16], sts, err);  assert (rdt[0+:16] ==      16'h3210) else $error("read data mismatch");
        man.read16(32'h00000022, rdt[0+:16], sts, err);  assert (rdt[0+:16] ==  16'h7654    ) else $error("read data mismatch");
        man.read32(32'h00000030, rdt[0+:32], sts, err);  assert (rdt[0+:32] ==  32'h76543210) else $error("read data mismatch");

        foreach(    man.rsp_que[i])  $display("DEBUG: man.rsp_que[%0d] = %p", i,     man.rsp_que[i]);
        foreach(mon_man.bus_que[i])  $display("DEBUG: mon_man.que[%0d] = %p", i, mon_man.bus_que[i]);
        foreach(mon_sub.bus_que[i])  $display("DEBUG: mon_sub.que[%0d] = %p", i, mon_sub.bus_que[i]);
    endtask: test_aligned

    task test_misaligned ();
        testname = "misaligned";
        $display("TEST: %s", testname);

            man.rsp_que.delete();
        mon_man.bus_que.delete();
        mon_sub.bus_que.delete();

        // misaligned write/read
        man.write16(32'h00000041,     16'h3210, sts, err);
        man.write16(32'h00000043, 16'h7654    , sts, err);
        man.read16 (32'h00000041, rdt[0+:16]  , sts, err);  assert (rdt[0+:16] ==      16'h3210) else $error("read data mismatch");
        man.read16 (32'h00000043, rdt[0+:16]  , sts, err);  assert (rdt[0+:16] ==  16'h7654    ) else $error("read data mismatch");
        man.read32 (32'h00000041, rdt[0+:32]  , sts, err);  assert (rdt[0+:32] ==  32'h76543210) else $error("read data mismatch");
        man.write32(32'h00000051, 32'h76543210, sts, err);
        man.read32 (32'h00000051, rdt[0+:32]  , sts, err);  assert (rdt[0+:32] ==  32'h76543210) else $error("read data mismatch");
        man.write32(32'h00000052, 32'h76543210, sts, err);
        man.read32 (32'h00000052, rdt[0+:32]  , sts, err);  assert (rdt[0+:32] ==  32'h76543210) else $error("read data mismatch");
        man.write32(32'h00000053, 32'h76543210, sts, err);
        man.read32 (32'h00000053, rdt[0+:32]  , sts, err);  assert (rdt[0+:32] ==  32'h76543210) else $error("read data mismatch");

        foreach(    man.rsp_que[i])  $display("DEBUG: man.rsp_que[%0d] = %p", i,     man.rsp_que[i]);
        foreach(mon_man.bus_que[i])  $display("DEBUG: mon_man.que[%0d] = %p", i, mon_man.bus_que[i]);
        foreach(mon_sub.bus_que[i])  $display("DEBUG: mon_sub.que[%0d] = %p", i, mon_sub.bus_que[i]);
    endtask: test_misaligned

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

        test_aligned;
        if (~ALIGNED) begin
            test_misaligned;
        end

        // end of test
        repeat (4) @(posedge clk);
        $finish();
    end: test

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

    // VIP
    tcb_lite_vip_manager              man (.man (tcb_man));
    tcb_lite_vip_monitor          mon_man (.mon (tcb_man));
    tcb_lite_vip_monitor          mon_sub (.mon (tcb_man));
    tcb_lite_vip_protocol_checker chk_man (.mon (tcb_man));
    tcb_lite_vip_protocol_checker chk_sub (.mon (tcb_sub));

    // connect singular interface to interface array
    tcb_lite_lib_passthrough pas [0:0] (
        .sub (tcb_sub),
        .man (tcb_mem)
    );

    // memory model subordinate
    tcb_lite_vip_memory #(
        .SIZE (2**8)
    ) mem (
        .sub (tcb_mem)
    );

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

    tcb_lite_lib_logsize2byteena #(
        .ALIGNED (ALIGNED)
    ) dut (
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

endmodule: tcb_lite_lib_logsize2byteena_tb
