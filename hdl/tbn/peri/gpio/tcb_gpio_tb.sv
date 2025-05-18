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

module tcb_gpio_tb
  import tcb_pkg::*;
  import tcb_vip_blocking_pkg::*;
#(
  // TCB widths
  int unsigned ADR = 32,
  int unsigned DAT = 32,
  // RW channels
  tcb_bus_channel_t CHN = TCB_HALF_DUPLEX
);

  // TODO: parameter propagation through virtual interfaces in classes
  // is not working well in Vivado 2023.1 thus this workaround

  // physical interface parameter
  localparam tcb_bus_t PHY1 = '{
    // protocol
    HSK.DLY: 0,
    // signal bus widths
    UNT: TCB_PAR_BUS_DEF.UNT,
    ADR: ADR,
    DAT: DAT,
    ALN: $clog2(DAT/TCB_PAR_BUS_DEF.UNT),
    // size/mode/order parameters
    SIZ: TCB_PAR_BUS_DEF.SIZ,
    MOD: TCB_PAR_BUS_DEF.MOD,
    ORD: TCB_PAR_BUS_DEF.ORD,
    // channel configuration
    CHN: TCB_PAR_BUS_DEF.CHN
  };

  localparam tcb_bus_t BUS = TCB_PAR_BUS_DEF;

  // GPIO width
  localparam int unsigned GW = 32;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // system signals
  logic clk;  // clock
  logic rst;  // reset
/*
  // TCB interface
  tcb_if #(.BUS (BUS)) tcb_man     (.clk (clk), .rst (rst));
  tcb_if #(.BUS (BUS)) tcb_man_wrc (.clk (clk), .rst (rst));
  tcb_if #(.BUS (BUS)) tcb_man_rdc (.clk (clk), .rst (rst));
*/
  // TODO: the above code should be used instead
  // TCB interfaces
  tcb_if tcb_man     (.clk (clk), .rst (rst));
  tcb_if tcb_man_wrc (.clk (clk), .rst (rst));
  tcb_if tcb_man_rdc (.clk (clk), .rst (rst));

  // parameterized class specialization
  typedef tcb_transfer_c #(.BUS (BUS)) tcb_s;

  // TCB class objects
  tcb_s obj_man;

////////////////////////////////////////////////////////////////////////////////
// data checking
////////////////////////////////////////////////////////////////////////////////

  // response
  logic [BUS.DAT-1:0] rdt;  // read data
  tcb_rsp_sts_def_t   sts;  // status response

  logic [ 8-1:0] rdt8 ;  //  8-bit read data
  logic [16-1:0] rdt16;  // 16-bit read data
  logic [32-1:0] rdt32;  // 32-bit read data

  // GPIO signals
  logic [GW-1:0] gpio_o;
  logic [GW-1:0] gpio_e;
  logic [GW-1:0] gpio_i;

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  initial          clk = 1'b1;
  always #(20ns/2) clk = ~clk;

  // test sequence
  initial
  begin
    // time dispaly formatting
    $timeformat(-9, 3, "ns", 12);
    // connect virtual interfaces
    obj_man = new("MAN", tcb_man);
    // reset sequence
    rst <= 1'b1;
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
    obj_man.check32('h08, 32'hxxxxxxxx, '0);  // read input register

    gpio_i <= GW'('h89abcdef);
    repeat (2) @(posedge clk);
    obj_man.check32('h08, 32'h89abcdef, '0);  // read input register

    gpio_i <= GW'('hfedcba98);
    repeat (2) @(posedge clk);
    obj_man.check32('h08, 32'hfedcba98, '0);  // read input register
    $display("(%t) INFO: reading/checking input end.", $time);

    // TODO: add automatic testbench status report (SUCCESS/FAILURE)

    // end simulation
    repeat (2) @(posedge clk);
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

  generate
  if (CHN == TCB_HALF_DUPLEX)
  begin: cmn

  // TCB GPIO
  tcb_cmn_gpio #(
    .GW      (GW),
    // implementation details
//    bit          CFG_MIN = 1'b0,  // minimalistic implementation
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

  end: cmn
  else
  begin: ind

  // TCB independent channel splitter
  tcb_lib_common2independent cmn2ind (
    // CRW subordinate port
    .tcb_cmn_sub (tcb_man),
    // IRW manager ports
    .tcb_rdc_man (tcb_man_rdc),
    .tcb_wrc_man (tcb_man_wrc)
  );

  // TCB GPIO
  tcb_ind_gpio #(
    .GW      (GW),
    // implementation details
//    bit          CFG_MIN = 1'b0,  // minimalistic implementation
    .CFG_CDC (2),
    // implementation device (ASIC/FPGA vendor/device)
    .CHIP    ("")
  ) gpio (
    // GPIO signals
    .gpio_o  (gpio_o),
    .gpio_e  (gpio_e),
    .gpio_i  (gpio_i),
    // TCB IRW interface
    .tcb_wrc (tcb_man_wrc),
    .tcb_rdc (tcb_man_rdc)
  );

  end: ind
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_gpio_tb
