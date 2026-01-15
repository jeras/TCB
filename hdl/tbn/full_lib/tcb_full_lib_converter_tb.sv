////////////////////////////////////////////////////////////////////////////////
// TCB-Full (Tightly Coupled Bus) library mode/alignment/order converter testbench
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

module tcb_full_lib_converter_tb
    import tcb_full_pkg::*;
    import tcb_full_vip_blocking_pkg::*;
#(
    // protocol
    parameter  int unsigned      MAN_DLY = TCB_PAR_BUS_DEF.HSK.DLY,  // response delay
    // signal widths
    parameter  int unsigned      MAN_UNT = TCB_PAR_BUS_DEF.UNT,  // data unit   width (byte width is 8 by default)
    parameter  int unsigned      MAN_ADR = TCB_PAR_BUS_DEF.ADR,  // address bus width
    parameter  int unsigned      MAN_DAT = TCB_PAR_BUS_DEF.DAT,  // data    bus width
    // PMA parameters for manager/subordinate
    parameter  int unsigned      MAN_ALN = TCB_PAR_BUS_DEF.ALN,  // TODO
    parameter  int unsigned      MAN_MIN = TCB_PAR_BUS_DEF.MIN,  // TODO
    parameter  tcb_bus_mode_t    MAN_MOD = TCB_PAR_BUS_DEF.MOD,  // manager     data position mode
    parameter  tcb_bus_order_t   MAN_ORD = TCB_PAR_BUS_DEF.ORD,  // manager     byte order
    // channel configuration
    parameter  tcb_bus_channel_t MAN_CHN = TCB_PAR_BUS_DEF.CHN,  // channel configuration

    // protocol
    parameter  int unsigned      SUB_DLY = TCB_PAR_BUS_DEF.HSK.DLY,  // response delay
    // signal widths
    parameter  int unsigned      SUB_UNT = TCB_PAR_BUS_DEF.UNT,  // data unit   width (byte width is 8 by default)
    parameter  int unsigned      SUB_ADR = TCB_PAR_BUS_DEF.ADR,  // address bus width
    parameter  int unsigned      SUB_DAT = TCB_PAR_BUS_DEF.DAT,  // data    bus width
    // PMA parameters for manager/subordinate
    parameter  int unsigned      SUB_ALN = TCB_PAR_BUS_DEF.ALN,  // TODO
    parameter  int unsigned      SUB_MIN = TCB_PAR_BUS_DEF.MIN,  // TODO
    parameter  tcb_bus_mode_t    SUB_MOD = TCB_PAR_BUS_DEF.MOD,  // subordinate data position mode
    parameter  tcb_bus_order_t   SUB_ORD = TCB_PAR_BUS_DEF.ORD,  // subordinate byte order
    // channel configuration
    parameter  tcb_bus_channel_t SUB_CHN = TCB_PAR_BUS_DEF.CHN   // channel configuration
);

    // manager physical interface parameter
    localparam tcb_bus_t MAN_BUS = '{
        // protocol
        HSK.DLY: MAN_DLY,
        // signal bus widths
        UNT: MAN_UNT,
        ADR: MAN_ADR,
        DAT: MAN_DAT,
        // size/mode/order parameters
        ALN: MAN_ALN,
        MIN: MAN_MIN,
        MOD: MAN_MOD,
        ORD: MAN_ORD,
        // channel configuration
        CHN: MAN_CHN
    };

    // subordinate physical interface parameter
    localparam tcb_bus_t SUB_BUS = '{
        // protocol
        HSK.DLY: SUB_DLY,
        // signal bus widths
        UNT: SUB_UNT,
        ADR: SUB_ADR,
        DAT: SUB_DAT,
        // size/mode/order parameters
        ALN: SUB_ALN,
        MIN: SUB_MIN,
        MOD: SUB_MOD,
        ORD: SUB_ORD,
        // channel configuration
        CHN: SUB_CHN
    };

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // system signals
    logic clk;  // clock
    logic rst;  // reset

    // TCB interfaces
    tcb_full_if #(.BUS (MAN_BUS)) tcb_man       (.clk (clk), .rst (rst));
    tcb_full_if #(.BUS (SUB_BUS)) tcb_sub       (.clk (clk), .rst (rst));
    tcb_full_if #(.BUS (SUB_BUS)) tcb_mem [0:0] (.clk (clk), .rst (rst));

    // TCB class objects
    tcb_transfer_c #(.BUS (MAN_BUS)) obj_man;
    tcb_transfer_c #(.BUS (SUB_BUS)) obj_sub;
    tcb_transfer_c #(.BUS (SUB_BUS)) obj_mem;

////////////////////////////////////////////////////////////////////////////////
// data checking
////////////////////////////////////////////////////////////////////////////////

    // response
    logic [tcb_man.BUS_BYT-1:0][tcb_man.BUS.UNT-1:0] rdt;  // read data
    tcb_rsp_sts_def_t                                sts;  // status response

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
        obj_man = new("MAN", tcb_man    );
        obj_sub = new("MON", tcb_sub    );
        obj_mem = new("MON", tcb_mem [0]);
        // reset sequence
        rst <= 1'b1;
        repeat (2) @(posedge clk);
        rst <= 1'b0;
        repeat (1) @(posedge clk);
        // write sequence
        obj_man.write8 (32'h00000010,        8'h10, sts);
        obj_man.write8 (32'h00000011,      8'h32  , sts);
        obj_man.write8 (32'h00000012,    8'h54    , sts);
        obj_man.write8 (32'h00000013,  8'h76      , sts);
        obj_man.write16(32'h00000020,     16'h3210, sts);
        obj_man.write16(32'h00000022, 16'h7654    , sts);
        obj_man.write32(32'h00000030, 32'h76543210, sts);
        // read sequence
        obj_man.read8  (32'h00000010, rdt[1-1:0]  , sts);
        obj_man.read8  (32'h00000011, rdt[1-1:0]  , sts);
        obj_man.read8  (32'h00000012, rdt[1-1:0]  , sts);
        obj_man.read8  (32'h00000013, rdt[1-1:0]  , sts);
        obj_man.read16 (32'h00000020, rdt[2-1:0]  , sts);
        obj_man.read16 (32'h00000022, rdt[2-1:0]  , sts);
        obj_man.read32 (32'h00000030, rdt[4-1:0]  , sts);
        // check sequence
        obj_man.check8 (32'h00000010,        8'h10, 1'b0);
        obj_man.check8 (32'h00000011,      8'h32  , 1'b0);
        obj_man.check8 (32'h00000012,    8'h54    , 1'b0);
        obj_man.check8 (32'h00000013,  8'h76      , 1'b0);
        obj_man.check32(32'h00000010, 32'h76543210, 1'b0);
        obj_man.check16(32'h00000020,     16'h3210, 1'b0);
        obj_man.check16(32'h00000022, 16'h7654    , 1'b0);
        obj_man.check32(32'h00000020, 32'h76543210, 1'b0);
        obj_man.check32(32'h00000030, 32'h76543210, 1'b0);
        // end of test
        repeat (4) @(posedge clk);
        $finish();
    end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

    // memory model subordinate
    tcb_full_vip_memory #(
        .SIZ (2**8)
    ) mem (
        .tcb (tcb_mem)
    );

    // connect interfaces to interface array
    tcb_full_lib_passthrough pas [0:0] (.sub (tcb_sub), .man (tcb_mem));

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

    tcb_full_lib_converter dut (
        .sub  (tcb_man),
        .man  (tcb_sub),
        .mal  ()
    );

//    tcb_full_lib_passthrough dut (
//      .sub  (tcb_man),
//      .man  (tcb_sub)
//    );

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

    initial
    begin
        $dumpfile("test.fst");
        $dumpvars;
    end

endmodule: tcb_full_lib_converter_tb
