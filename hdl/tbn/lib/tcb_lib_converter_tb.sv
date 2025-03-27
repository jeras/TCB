////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library mode/alignment/order converter testbench
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

module tcb_lib_converter_tb
  import tcb_pkg::*;
  import tcb_vip_pkg::*;
#(
  // protocol
  int unsigned      MAN_DLY = TCB_PAR_PHY_DEF.DLY,  // response delay
  // signal widths
  int unsigned      MAN_SLW = TCB_PAR_PHY_DEF.SLW,  // selection   width (byte width is 8 by default)
  int unsigned      MAN_ABW = TCB_PAR_PHY_DEF.ABW,  // address bus width
  int unsigned      MAN_DBW = TCB_PAR_PHY_DEF.DBW,  // data    bus width
  int unsigned      MAN_ALW = TCB_PAR_PHY_DEF.ALW,  // alignment width
  // data packing parameters for manager/subordinate
  tcb_par_size_t    MAN_SIZ = TCB_PAR_PHY_DEF.SIZ,  // manager     transfer size encoding
  tcb_par_mode_t    MAN_MOD = TCB_PAR_PHY_DEF.MOD,  // manager     data position mode
  tcb_par_order_t   MAN_ORD = TCB_PAR_PHY_DEF.ORD,  // manager     byte order
  // channel configuration
  tcb_par_channel_t MAN_CHN = TCB_PAR_PHY_DEF.CHN,  // channel configuration

  // protocol
  int unsigned      SUB_DLY = TCB_PAR_PHY_DEF.DLY,  // response delay
  // signal widths
  int unsigned      SUB_SLW = TCB_PAR_PHY_DEF.SLW,  // selection   width (byte width is 8 by default)
  int unsigned      SUB_ABW = TCB_PAR_PHY_DEF.ABW,  // address bus width
  int unsigned      SUB_DBW = TCB_PAR_PHY_DEF.DBW,  // data    bus width
  int unsigned      SUB_ALW = TCB_PAR_PHY_DEF.ALW,  // alignment width
  // data packing parameters for manager/subordinate
  tcb_par_size_t    SUB_SIZ = TCB_PAR_PHY_DEF.SIZ,  // subordinate transfer size encoding
  tcb_par_mode_t    SUB_MOD = TCB_PAR_PHY_DEF.MOD,  // subordinate data position mode
  tcb_par_order_t   SUB_ORD = TCB_PAR_PHY_DEF.ORD,  // subordinate byte order
  // channel configuration
  tcb_par_channel_t SUB_CHN = TCB_PAR_PHY_DEF.CHN   // channel configuration
);

  // manager physical interface parameter
  localparam tcb_par_phy_t MAN_PHY = '{
    // protocol
    DLY: MAN_DLY,
    // signal bus widths
    SLW: MAN_SLW,
    ABW: MAN_ABW,
    DBW: MAN_DBW,
    ALW: MAN_ALW,
    // size/mode/order parameters
    SIZ: MAN_SIZ,
    MOD: MAN_MOD,
    ORD: MAN_ORD,
    // channel configuration
    CHN: MAN_CHN
  };

  // subordinate physical interface parameter
  localparam tcb_par_phy_t SUB_PHY = '{
    // protocol
    DLY: SUB_DLY,
    // signal bus widths
    SLW: SUB_SLW,
    ABW: SUB_ABW,
    DBW: SUB_DBW,
    ALW: SUB_ALW,
    // size/mode/order parameters
    SIZ: SUB_SIZ,
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
  tcb_if #(.PHY (MAN_PHY)) tcb_man       (.clk (clk), .rst (rst));
  tcb_if #(.PHY (SUB_PHY)) tcb_sub       (.clk (clk), .rst (rst));
  tcb_if #(.PHY (SUB_PHY)) tcb_mem [0:0] (.clk (clk), .rst (rst));

  // TCB class objects
  tcb_transfer_c #(.PHY (MAN_PHY)) obj_man;
  tcb_transfer_c #(.PHY (SUB_PHY)) obj_sub;
  tcb_transfer_c #(.PHY (SUB_PHY)) obj_mem;

////////////////////////////////////////////////////////////////////////////////
// data checking
////////////////////////////////////////////////////////////////////////////////

  // response
  logic [tcb_man.PHY_BEW-1:0][tcb_man.PHY.SLW-1:0] rdt;  // read data
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
  tcb_vip_memory      mem       (.tcb (tcb_mem));

  // connect interfaces to interface array
  tcb_lib_passthrough pas [0:0] (.sub (tcb_sub), .man (tcb_mem));

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

  tcb_lib_converter dut (
    .sub  (tcb_man),
    .man  (tcb_sub),
    .mal  ()
  );

//  tcb_lib_passthrough dut (
//    .sub  (tcb_man),
//    .man  (tcb_sub)
//  );

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_lib_converter_tb
