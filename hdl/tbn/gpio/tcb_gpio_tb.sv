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
  import tcb_vip_pkg::*;
#(
  // TCB widths
  int unsigned ABW = 32,
  int unsigned DBW = 32
);

  // TODO: parameter propagation through virtual interfaces in classes
  // is not working well thus this workaround

  // physical interface parameter
  localparam tcb_par_phy_t PHY1 = '{
    // signal bus widths
    SLW: TCB_PAR_PHY_DEF.SLW,
    ABW: ABW,
    DBW: DBW,
    // TCB parameters
    DLY: 0,
    // mode/alignment/order parameters
    MOD: TCB_PAR_PHY_DEF.MOD,
    SIZ: TCB_PAR_PHY_DEF.SIZ,
    ORD: TCB_PAR_PHY_DEF.ORD,
    LGN: TCB_PAR_PHY_DEF.LGN
  };

  localparam tcb_par_phy_t PHY = TCB_PAR_PHY_DEF;

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
  tcb_if #(.PHY (PHY)) tcb (.clk (clk), .rst (rst));
*/
  // TODO: the above code should be used instead
  // TCB interfaces
  tcb_if tcb_man (.clk (clk), .rst (rst));

  // parameterized class specialization
  typedef tcb_transfer_c #(.PHY (PHY)) tcb_s;

  // TCB class objects
  tcb_s obj_man;

////////////////////////////////////////////////////////////////////////////////
// data checking
////////////////////////////////////////////////////////////////////////////////

  // response
  logic [PHY.DBW-1:0] rdt;  // read data
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
    // connect virtual interfaces
    obj_man = new("MAN", tcb_man);
    // reset sequence
    rst <= 1'b1;
    repeat (2) @(posedge clk);
    rst <= 1'b0;
    repeat (1) @(posedge clk);

    // configure outputs
    obj_man.write32('h00, 32'h01234567, sts);  // write output register
    obj_man.write32('h04, 32'h76543210, sts);  // write enable register

    // read GPIO input status
    obj_man.read32('h08, rdt32, sts);  // read input register
    if (GW'(rdt) != GW'('hxxxxxxxx))  $display("ERROR: readout error rdt=%8h, ref=%8h", rdt, GW'('hxxxxxxxx));

    gpio_i <= GW'('h89abcdef);
    repeat (2) @(posedge clk);
    obj_man.read32('h08, rdt32, sts);  // read input register
    if (GW'(rdt) != GW'('h89abcdef))  $display("ERROR: readout error rdt=%8h, ref=%8h", rdt, GW'('h89abcdef));

    gpio_i <= GW'('hfedcba98);
    repeat (2) @(posedge clk);
    obj_man.read32('h08, rdt32, sts);  // read input register
    if (GW'(rdt) != GW'('hfedcba98))  $display("ERROR: readout error rdt=%8h, ref=%8h", rdt, GW'('hfedcba98));

    repeat (2) @(posedge clk);
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// DUT instance
////////////////////////////////////////////////////////////////////////////////

  // TCB GPIO
  tcb_gpio #(
    .GW      (GW),
    // implementation details
//    bit          CFG_MIN = 1'b0,  // minimalistic implementation
    .CFG_CDC (2),
    // implementation device (ASIC/FPGA vendor/device)
    .CHIP    ("")
  ) gpio (
    // GPIO signals
    .gpio_o (gpio_o),
    .gpio_e (gpio_e),
    .gpio_i (gpio_i),
    // TCB interface
    .tcb    (tcb_man)
  );

////////////////////////////////////////////////////////////////////////////////
// VCD/FST waveform trace
////////////////////////////////////////////////////////////////////////////////

  initial
  begin
    $dumpfile("test.fst");
    $dumpvars;
  end

endmodule: tcb_gpio_tb
