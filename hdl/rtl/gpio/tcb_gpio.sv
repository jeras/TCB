////////////////////////////////////////////////////////////////////////////////
// TCB interface GPIO controller
//
// NOTE: In case this module is connected to asynchronous signals,
//       the input signals `gpio_i` require a CDC synchronizer.
//       By default a 2 FF synchronizer is implemented by the CFG_CDC parameter.
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

module tcb_gpio #(
  // GPIO parameters
  int unsigned GW = 32,   // GPIO width
  int unsigned CFG_CDC = 2,     // implement clock domain crossing stages (0 - bypass)
  // TCB parameters
  bit          CFG_RSP_REG = 1'b1,  // register response path (by default the response is registered giving a DLY of 1)
  bit          CFG_RSP_MIN = 1'b0,  // minimalistic response implementation
  // implementation device (ASIC/FPGA vendor/device)
  string       CHIP = ""
)(
  // GPIO signals
  output logic [GW-1:0] gpio_o,
  output logic [GW-1:0] gpio_e,
  input  logic [GW-1:0] gpio_i,
  // TCB interface
  tcb_if.sub tcb
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
generate
  if (tcb.PHY.DLY != 1)  $error("ERROR: %m parameter DLY validation failed");
  if (tcb.PHY.DBW < GW)  $error("ERROR: %m parameter GW exceeds the data bus width");
endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// clock domain crossing
////////////////////////////////////////////////////////////////////////////////

  // read value
  logic [GW-1:0] gpio_r;

generate
if (CFG_CDC > 0) begin: gen_cdc

  // GPIO input synchronizer
  if ((CHIP == "ARTIX_XPM") || (CHIP == "ARTIX_GEN")) begin: gen_artix

    // xpm_cdc_array_single: Single-bit Array Synchronizer
    // Xilinx Parameterized Macro, version 2021.2
    xpm_cdc_array_single #(
     .DEST_SYNC_FF   (CFG_CDC),  // DECIMAL; range: 2-10
     .INIT_SYNC_FF   (0),        // DECIMAL; 0=disable simulation init values, 1=enable simulation init values
     .SIM_ASSERT_CHK (0),        // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
     .SRC_INPUT_REG  (0),        // DECIMAL; 0=do not register input, 1=register input
     .WIDTH          (GW)        // DECIMAL; range: 1-1024
    ) gpio_cdc (
     .src_clk  (tcb.clk),
     .src_in   (gpio_i),
     .dest_clk (tcb.clk),
     .dest_out (gpio_r)
    );

  end: gen_artix
  else begin: gen_default

    // temporary signal for synchronization
    logic [CFG_CDC-2:0][GW-1:0] gpio_t;

    // asynchronous input synchronization
    always_ff @(posedge tcb.clk, posedge tcb.rst)
    if (tcb.rst) begin
      {gpio_r, gpio_t} <= '0;
    end else begin
      {gpio_r, gpio_t} <= {gpio_t, gpio_i};
    end

  end: gen_default

end: gen_cdc
else begin: gen_nocdc

  // bypass CDC code
  assign gpio_r = gpio_i;

end: gen_nocdc
endgenerate

////////////////////////////////////////////////////////////////////////////////
// TCB access
////////////////////////////////////////////////////////////////////////////////

// read access
generate
// minimalistic implementation
if (CFG_RSP_MIN) begin: gen_rsp_min

  // only the GPIO input can be read
  assign tcb.rdt = gpio_r;

end: gen_rsp_min
// normal implementation
else begin: gen_rsp_nrm

  // GPIO output/enable registers and GPIO input are decoded
  always_comb
  case (tcb.req.adr[4-1:0])
    4'h0:    tcb.rsp.rdt = gpio_o;
    4'h4:    tcb.rsp.rdt = gpio_e;
    4'h8:    tcb.rsp.rdt = gpio_r;
    default: tcb.rsp.rdt = 'x;
  endcase

  // read data response
  assign tcb.rsp.rdt = tcb.rsp.rdt;

end: gen_rsp_nrm
endgenerate

  // write output and output enable
  always_ff @(posedge tcb.clk, posedge tcb.rst)
  if (tcb.rst) begin
    gpio_o <= '0;
    gpio_e <= '0;
  end else if (tcb.trn) begin
    if (tcb.req.wen) begin
      // write access
      case (tcb.req.adr[4-1:0])
        4'h0:    gpio_o <= tcb.req.wdt[GW-1:0];
        4'h4:    gpio_e <= tcb.req.wdt[GW-1:0];
        default: ;  // do nothing
      endcase
    end
  end

  // controller response is immediate
  assign tcb.rdy = 1'b1;

  // there are no error cases
  assign tcb.rsp.sts = '0;

endmodule: tcb_gpio