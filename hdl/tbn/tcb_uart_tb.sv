////////////////////////////////////////////////////////////////////////////////
// R5P testbench for core module
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

module tcb_uart_tb
  import tcb_pkg::*;
#(
  // bus widths
  int unsigned AW = 32,    // address width
  int unsigned DW = 32,    // data    width
  int unsigned BW = DW/8,  // byte e. width
  // response delay
  int unsigned DLY = 1
);

  // UART data width
  localparam int unsigned UDW = 8;

  // system signals
  logic clk;  // clock
  logic rst;  // reset

  // TCB interface
  tcb_if #(.AW (AW), .DW (DW)) bus (.clk (clk), .rst (rst));

  // response check values
  tcb_rsp_t rsp;

  // UART signals
  logic uart_o;
  logic uart_e;

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

  // clock
  initial          clk = 1'b1;
  always #(20ns/2) clk = ~clk;

  // reset
  initial
  begin
    // reset sequence
    rst <= 1'b1;
    repeat (4) @(posedge clk);
    rst <= 1'b0;
    repeat (1) @(posedge clk);
    fork
      // start TCB requests
      begin: test_req
        //         wen,  adr,     ben,          wdt, len
        man.req('{1'b1, 'h00, 4'b1111, 32'h01234567, 0});  // write output register
        man.req('{1'b1, 'h04, 4'b1111, 32'h76543210, 0});  // write enable register
        man.req('{1'b0, 'h08, 4'b1111, 32'hxxxxxxxx, 0});  // read input register
        man.req('{1'b0, 'h08, 4'b1111, 32'hxxxxxxxx, 0});  // read input register
        man.req('{1'b0, 'h08, 4'b1111, 32'hxxxxxxxx, 0});  // read input register
      end: test_req
      // set GPIO input values
//      begin: test_gpio
//        repeat (2) @(negedge clk);
//        gpio_i <= GW'('h89abcdef);
//        repeat (1) @(negedge clk);
//        gpio_i <= GW'('hfedcba98);
//      end: test_gpio
      // check TCB responses
      begin: test_rsp
        man.rsp(rsp);  if (rsp.rdt !== DW'('hxxxxxxxx))  $display("ERROR: readout error rdt=%8h, ref=%8h", rsp.rdt, DW'('hxxxxxxxx));
        man.rsp(rsp);  if (rsp.rdt !== DW'('h89abcdef))  $display("ERROR: readout error rdt=%8h, ref=%8h", rsp.rdt, DW'('h89abcdef));
        man.rsp(rsp);  if (rsp.rdt !== DW'('hfedcba98))  $display("ERROR: readout error rdt=%8h, ref=%8h", rsp.rdt, DW'('hfedcba98));
      end: test_rsp
    join
    repeat (8) @(posedge clk);
    $finish();
  end

  tcb_man #(
    .DLY  (DLY)
  ) man (
    .bus  (bus)
  );

  tcb_uart #(
    .DW      (UDW)
  ) uart (
    // UART signals
    .uart_txd (uart_txd),
    .uart_rxd (uart_rxd),
    // system bus interface
    .bus      (bus)
  );

endmodule: tcb_uart_tb