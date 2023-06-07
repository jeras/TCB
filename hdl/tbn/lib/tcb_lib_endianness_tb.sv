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

module tcb_lib_endianness_tb
  import tcb_pkg::*;
  import tcb_vip_pkg::*;
#(
  // TCB widths
  tcb_par_phy_t PHY = '{ABW: 32, DBW: 32, SLW: 8},
  //tcb_par_log_t LOG = '{},
  // response delay
  int unsigned DLY = 1
);

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  tcb_if #(.PHY (PHY), .DLY (DLY)) tcb_man       (.clk (clk), .rst (rst));
  tcb_if #(.PHY (PHY), .DLY (DLY)) tcb_sub       (.clk (clk), .rst (rst));
  tcb_if #(.PHY (PHY), .DLY (DLY)) tcb_mem [0:0] (.clk (clk), .rst (rst));

  tcb_vip_pkg::tcb_transfer_c #(.PHY (PHY)) obj_man;
  tcb_vip_pkg::tcb_transfer_c #(.PHY (PHY)) obj_sub;
  tcb_vip_pkg::tcb_transfer_c #(.PHY (PHY)) obj_mem;

////////////////////////////////////////////////////////////////////////////////
// data checking function
////////////////////////////////////////////////////////////////////////////////

  // response
  logic [PHY.DBW-1:0] rdt;  // read data
  logic               err;  // error response

  logic [ 8-1:0] rdt8 ;  //  8-bit read data
  logic [16-1:0] rdt16;  // 16-bit read data
  logic [32-1:0] rdt32;  // 32-bit read data

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  initial          clk = 1'b1;
  always #(20ns/2) clk = ~clk;

  // test sequence
  initial
  begin
    // reset
    rst = 1'b1;
    // connect virtual interfaces
    obj_man = new("MAN", tcb_man    );
    obj_sub = new("MON", tcb_sub    );
    obj_mem = new("MON", tcb_mem [0]);
    // reset sequence
    repeat (2) @(posedge clk);
    rst = 1'b0;
    repeat (1) @(posedge clk);
    // write sequence
    obj_man.write8 (32'h00000010,        8'h10, err);
    obj_man.write8 (32'h00000011,      8'h32  , err);
    obj_man.write8 (32'h00000012,    8'h54    , err);
    obj_man.write8 (32'h00000013,  8'h76      , err);
    obj_man.write16(32'h00000020,     16'h3210, err);
    obj_man.write16(32'h00000022, 16'h7654    , err);
    obj_man.write32(32'h00000030, 32'h76543210, err);
    // read sequence
    obj_man.read8  (32'h00000010, rdt8        , err);  
    obj_man.read8  (32'h00000011, rdt8        , err);
    obj_man.read8  (32'h00000012, rdt8        , err);
    obj_man.read8  (32'h00000013, rdt8        , err);
    obj_man.read16 (32'h00000020, rdt16       , err);
    obj_man.read16 (32'h00000022, rdt16       , err);
    obj_man.read32 (32'h00000030, rdt32       , err);
    // read sequence
    obj_man.check8 (32'h00000010,        8'h10, 1'b0);
    obj_man.check8 (32'h00000011,      8'h32  , 1'b0);
    obj_man.check8 (32'h00000012,    8'h54    , 1'b0);
    obj_man.check8 (32'h00000013,  8'h76      , 1'b0);
    obj_man.check32(32'h00000010, 32'h76543210, 1'b0);
    obj_man.check16(32'h00000020,     16'h3210, 1'b0);
    obj_man.check16(32'h00000022, 16'h7654    , 1'b0);
    obj_man.check32(32'h00000020, 32'h76543210, 1'b0);
    obj_man.check32(32'h00000030, 32'h76543210, 1'b0);
    // read sequence
    $display("32'h%08X", rdt);
    repeat (4) @(posedge clk);
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  tcb_vip_mem         mem       (.tcb (tcb_mem));  // subordinate

  // connect interfaces to interface array
  tcb_lib_passthrough pas [0:0] (.sub (tcb_sub), .man (tcb_mem));

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

  tcb_lib_endianness dut (
    .sub  (tcb_man),
    .man  (tcb_sub)
  );

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_lib_endianness_tb
