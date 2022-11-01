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
  import tcb_vip_pkg::*;
#(
  // TCB widths
  int unsigned ABW = 32,     // address bus width
  int unsigned DBW = 32,     // data    bus width
  int unsigned BEW = DBW/8,  // byte enable width
  // response delay
  int unsigned DLY = 1
);

  // GPIO width
  localparam int unsigned GW = 32;

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // TCB interface
  tcb_if #(.ABW (ABW), .DBW (DBW), .DLY (DLY)) tcb (.clk (clk), .rst (rst));

  // TCB response check values
  logic [DBW-1:0] rdt;
  logic           err;

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
    // reset sequence
    rst <= 1'b1;
    repeat (2) @(posedge clk);
    rst <= 1'b0;
    repeat (1) @(posedge clk);

    // configure outputs
    man.write('h00, 4'b1111, 32'h01234567, err);  // write output register
    man.write('h04, 4'b1111, 32'h76543210, err);  // write enable register

    // read GPIO input status
    man.read('h08, 4'b1111, rdt, err);  // read input register
    if (GW'(rdt) != GW'('hxxxxxxxx))  $display("ERROR: readout error rdt=%8h, ref=%8h", rdt, GW'('hxxxxxxxx));

    gpio_i <= GW'('h89abcdef);
    repeat (2) @(posedge clk);
    man.read('h08, 4'b1111, rdt, err);  // read input register
    if (GW'(rdt) != GW'('h89abcdef))  $display("ERROR: readout error rdt=%8h, ref=%8h", rdt, GW'('h89abcdef));

    gpio_i <= GW'('hfedcba98);
    repeat (2) @(posedge clk);
    man.read('h08, 4'b1111, rdt, err);  // read input register
    if (GW'(rdt) != GW'('hfedcba98))  $display("ERROR: readout error rdt=%8h, ref=%8h", rdt, GW'('hfedcba98));

    repeat (2) @(posedge clk);
    $finish();
  end

////////////////////////////////////////////////////////////////////////////////
// VIP instances
////////////////////////////////////////////////////////////////////////////////

  // manager
  tcb_vip_man man (.tcb (tcb));

////////////////////////////////////////////////////////////////////////////////
// DUT instances
////////////////////////////////////////////////////////////////////////////////

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
    .tcb    (tcb)
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