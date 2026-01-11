////////////////////////////////////////////////////////////////////////////////
// TCB GPIO testbench
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

module tcb_peri_gpio_tb
    import tcb_pkg::*;
    import tcb_vip_blocking_pkg::*;
#(
    // TCB widths
    int unsigned ADR = 32,
    int unsigned DAT = 32
);

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

    // GPIO width
    localparam int unsigned GW = 32;

    // configuration parameter
    localparam tcb_cfg_t CFG = '{
        // handshake parameter
        HSK: '{
            DLY: 0,
            HLD: 1'b0
        },
        // bus parameter
        BUS: '{
            ADR: TCB_BUS_DEF.ADR,
            DAT: TCB_BUS_DEF.DAT,
            LEN: TCB_BUS_DEF.LEN,
            LCK: TCB_LCK_PRESENT,
            CHN: TCB_CHN_HALF_DUPLEX,
            AMO: TCB_AMO_ABSENT,
            PRF: TCB_PRF_ABSENT,
            NXT: TCB_NXT_ABSENT,
            MOD: TCB_MOD_LOG_SIZE,
            ORD: TCB_ORD_DESCENDING,
            NDN: TCB_NDN_BI_NDN
        },
        // physical interface parameter
        PMA: TCB_PMA_DEF
    };

    localparam tcb_vip_t VIP = '{
        DRV: 1'b1
    };

//    typedef tcb_c #(HSK, BUS_SIZ, PMA)::req_t req_t;
//    typedef tcb_c #(HSK, BUS_SIZ, PMA)::rsp_t rsp_t;

    // local request/response types are copies of packaged defaults
    typedef tcb_req_t req_t;
    typedef tcb_rsp_t rsp_t;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // system signals (initialized)
    logic clk = 1'b1;  // clock
    logic rst = 1'b1;  // reset

    string testname = "none";

    // TCB interfaces
    tcb_if #(tcb_cfg_t, CFG, req_t, rsp_t) tcb_man (.clk (clk), .rst (rst));

    // parameterized class specialization (blocking API)
    typedef tcb_vip_blocking_c #(tcb_cfg_t, CFG, req_t, rsp_t) tcb_man_s;

    // TCB class objects
    tcb_man_s obj_man = new(tcb_man, "MAN");

    // response
    logic [tcb_man.CFG_BUS_BYT-1:0][8-1:0] rdt;  // read data
    tcb_rsp_sts_t                          sts;  // status response

////////////////////////////////////////////////////////////////////////////////
// data checking
////////////////////////////////////////////////////////////////////////////////

    // GPIO signals
    logic [GW-1:0] gpio_o;
    logic [GW-1:0] gpio_e;
    logic [GW-1:0] gpio_i;

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

    // clock
    always #(20ns/2) clk = ~clk;

    // test sequence
    initial
    begin: test
        // time dispaly formatting
        $timeformat(-9, 3, "ns", 12);
        // reset sequence
        repeat (2) @(posedge clk);
        rst <= 1'b0;
        repeat (1) @(posedge clk);

        // write configuration (output and enable registers)
        $display("(%t) INFO: writing configuration begin.", $time);
        obj_man.write32('h00, 32'h01234567, sts);  // write output register
        obj_man.write32('h04, 32'h76543210, sts);  // write enable register
        $display("(%t) INFO: writing configuration end.", $time);
        repeat (1) @(posedge clk);

        // check configuration (output and enable registers)
        $display("(%t) INFO: reading/checking configuration begin.", $time);
        obj_man.check32('h00, 32'h01234567, sts);  // write output register
        obj_man.check32('h04, 32'h76543210, sts);  // write enable register
        $display("(%t) INFO: reading/checking configuration end.", $time);
        repeat (1) @(posedge clk);

        // read/check GPIO input status
        $display("(%t) INFO: reading/checking input begin.", $time);
        #10 gpio_i = GW'('h89abcdef);
        repeat (2) @(posedge clk);
        obj_man.check32('h08, 32'h89abcdef, '0);  // read input register
        #10 gpio_i = GW'('hfedcba98);
        repeat (2) @(posedge clk);
        obj_man.check32('h08, 32'hfedcba98, '0);  // read input register
        $display("(%t) INFO: reading/checking input end.", $time);

        // TODO: add automatic testbench status report (SUCCESS/FAILURE)

        // end simulation
        repeat (4) @(posedge clk);
        $finish();
    end: test

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

    tcb_vip_protocol_checker chk_man (
        .tcb (tcb_man)
    );

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

    // TCB GPIO
    tcb_peri_gpio #(
        .GW      (GW),
        // implementation details
//        bit          CFG_MIN = 1'b0,  // minimalistic implementation
        .CFG_CDC (2),
        // implementation device (ASIC/FPGA vendor/device)
        .CHIP    ("")
    ) gpio (
        // GPIO signals
        .gpio_o  (gpio_o),
        .gpio_e  (gpio_e),
        .gpio_i  (gpio_i),
        // TCB interface
        .tcb     (tcb_man)
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

endmodule: tcb_peri_gpio_tb
