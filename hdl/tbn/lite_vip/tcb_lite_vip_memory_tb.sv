////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) VIP (Verification IP) memory TestBench
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

module tcb_lite_vip_memory_tb
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

    // TCB configurations               '{HSK: '{DLY, HLD}, BUS: '{MOD, CTL, ADR, DAT, STS}}
    localparam tcb_lite_cfg_t MAN_CFG = '{HSK: '{DLY, HLD}, BUS: '{MOD, CTL, ADR, DAT, STS}};

    localparam bit VIP = 1'b1;

    // slave interface number
    localparam int unsigned  IFN = 1;
    // write mask (which interfaces are allowed write access)
    localparam bit [IFN-1:0] WRM = '1;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // system signals
    logic clk = 1'b1;  // clock
    logic rst = 1'b1;  // reset

    // TCB interfaces
    tcb_lite_if #(MAN_CFG, VIP) tcb [IFN-1:0] (.clk (clk), .rst (rst));

    // testbench status signals
    string       testname;  // test name

    // response
    logic [DAT-1:0] rdt;  // read data
    logic [STS-1:0] sts;  // response status
    logic           err;  // response error

    // data organized into packed bytes
    typedef logic [DAT-1:0] data_t;

////////////////////////////////////////////////////////////////////////////////
// test nonblocking API
////////////////////////////////////////////////////////////////////////////////

    task automatic test_nonblocking;
    endtask: test_nonblocking

////////////////////////////////////////////////////////////////////////////////
// test blocking API
////////////////////////////////////////////////////////////////////////////////

    task automatic test_blocking;
        // write sequence
        testname = "write sequence";
        $display("TEST: %s", testname);

        // manager (blocking API)
        man[0].write8 (32'h00000010,        8'h10, sts, err);
        man[0].write8 (32'h00000011,      8'h32  , sts, err);
        man[0].write8 (32'h00000012,    8'h54    , sts, err);
        man[0].write8 (32'h00000013,  8'h76      , sts, err);
        man[0].write16(32'h00000020,     16'h3210, sts, err);
        man[0].write16(32'h00000022, 16'h7654    , sts, err);
        man[0].write32(32'h00000030, 32'h76543210, sts, err);

        man[0].read8 (32'h00000010, rdt[0+:8 ], sts, err);  assert (rdt[0+:8 ] ==         8'h10) else $error("read data mismatch");
        man[0].read8 (32'h00000011, rdt[0+:8 ], sts, err);  assert (rdt[0+:8 ] ==       8'h32  ) else $error("read data mismatch");
        man[0].read8 (32'h00000012, rdt[0+:8 ], sts, err);  assert (rdt[0+:8 ] ==     8'h54    ) else $error("read data mismatch");
        man[0].read8 (32'h00000013, rdt[0+:8 ], sts, err);  assert (rdt[0+:8 ] ==   8'h76      ) else $error("read data mismatch");
        man[0].read16(32'h00000020, rdt[0+:16], sts, err);  assert (rdt[0+:16] ==      16'h3210) else $error("read data mismatch");
        man[0].read16(32'h00000022, rdt[0+:16], sts, err);  assert (rdt[0+:16] ==  16'h7654    ) else $error("read data mismatch");
        man[0].read32(32'h00000030, rdt[0+:32], sts, err);  assert (rdt[0+:32] ==  32'h76543210) else $error("read data mismatch");

        // misaligned write/read
        man[0].write16(32'h00000041,     16'h3210, sts, err);
        man[0].write16(32'h00000043, 16'h7654    , sts, err);
        man[0].read16 (32'h00000041, rdt[0+:16]  , sts, err);  assert (rdt[0+:16] ==      16'h3210) else $error("read data mismatch");
        man[0].read16 (32'h00000043, rdt[0+:16]  , sts, err);  assert (rdt[0+:16] ==  16'h7654    ) else $error("read data mismatch");
        man[0].read32 (32'h00000041, rdt[0+:32]  , sts, err);  assert (rdt[0+:32] ==  32'h76543210) else $error("read data mismatch");
        man[0].write32(32'h00000051, 32'h76543210, sts, err);
        man[0].read32 (32'h00000051, rdt[0+:32]  , sts, err);  assert (rdt[0+:32] ==  32'h76543210) else $error("read data mismatch");
        man[0].write32(32'h00000052, 32'h76543210, sts, err);
        man[0].read32 (32'h00000052, rdt[0+:32]  , sts, err);  assert (rdt[0+:32] ==  32'h76543210) else $error("read data mismatch");
        man[0].write32(32'h00000053, 32'h76543210, sts, err);
        man[0].read32 (32'h00000053, rdt[0+:32]  , sts, err);  assert (rdt[0+:32] ==  32'h76543210) else $error("read data mismatch");

        foreach(man[0].rsp_que[i])  $display("DEBUG: man.rsp_que[%0d] = %p", i, man[0].rsp_que[i]);
        foreach(mon[0].bus_que[i])  $display("DEBUG: mon.bus_que[%0d] = %p", i, mon[0].bus_que[i]);

    endtask: test_blocking

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

    // clock
    always #(20ns/2) clk = ~clk;

    // test sequence
    initial
    begin
        // reset sequence
        repeat (2) @(posedge clk);
        /* verilator lint_off INITIALDLY */
        rst <= 1'b0;
        /* verilator lint_on INITIALDLY */
        repeat (1) @(posedge clk);

        // tests
        test_nonblocking;
        test_blocking;

        repeat (2) @(posedge clk);
        $finish();
    end

////////////////////////////////////////////////////////////////////////////////
// manager/subordinate VIP devices
////////////////////////////////////////////////////////////////////////////////

    // VIP
    tcb_lite_vip_manager          man [IFN-1:0] (.man (tcb));
    tcb_lite_vip_monitor          mon [IFN-1:0] (.mon (tcb));
    tcb_lite_vip_protocol_checker chk [IFN-1:0] (.mon (tcb));

    // subordinate  VIP
    tcb_lite_vip_memory #(
        .IFN (IFN),
        .WRM (WRM)
    ) sub (
        .tcb (tcb)
    );

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

    initial
    begin
        $dumpfile("test.fst");
        $dumpvars;
    end

endmodule: tcb_lite_vip_memory_tb
