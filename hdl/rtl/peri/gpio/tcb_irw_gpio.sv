////////////////////////////////////////////////////////////////////////////////
// TCB interface (independent RW channels): GPIO controller
//
// NOTE: In case this module is connected to asynchronous signals,
//       the input signals `gpio_i` require a CDC synchronizer.
//       By default a 2 FF synchronizer is implemented by the CFG_CDC parameter.
////////////////////////////////////////////////////////////////////////////////
// Copyright 2023 Iztok Jeras
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

module tcb_ind_gpio #(
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
  // TCB IRW interface
  tcb_if.sub tcb_rdc,
  tcb_if.sub tcb_wrc
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
generate
  if (tcb_wrc.PHY.DLY !=  0)  $error("ERROR: %m parameter DLY validation failed");
  if (tcb_rdc.PHY.DLY !=  0)  $error("ERROR: %m parameter DLY validation failed");
  if (tcb_wrc.PHY.DBW != 32)  $error("ERROR: %m parameter DBW validation failed");
  if (tcb_rdc.PHY.DBW != 32)  $error("ERROR: %m parameter DBW validation failed");
  if (             GW >  32)  $error("ERROR: %m parameter GW exceeds the data bus width");
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
     .src_clk  (tcb_rdc.clk),
     .src_in   (gpio_i),
     .dest_clk (tcb_rdc.clk),
     .dest_out (gpio_r)
    );

  end: gen_artix
  else begin: gen_default

    // temporary signal for synchronization
    logic [CFG_CDC-2:0][GW-1:0] gpio_t;

    // asynchronous input synchronization
    always_ff @(posedge tcb_rdc.clk, posedge tcb_rdc.rst)
    if (tcb_rdc.rst) begin
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
// TCB read access
////////////////////////////////////////////////////////////////////////////////

// read access
generate
// minimalistic implementation
if (CFG_RSP_MIN) begin: gen_rsp_min

  // only the GPIO input can be read
  assign tcb_rdc.rdt = gpio_r;

end: gen_rsp_min
// normal implementation
else begin: gen_rsp_nrm

  // GPIO output/enable registers and GPIO input are decoded
  always_comb
  case (tcb_rdc.req.adr[4-1:0])
    4'h0:    tcb_rdc.rsp.rdt = gpio_o;
    4'h4:    tcb_rdc.rsp.rdt = gpio_e;
    4'h8:    tcb_rdc.rsp.rdt = gpio_r;
    default: tcb_rdc.rsp.rdt = 'x;
  endcase

end: gen_rsp_nrm
endgenerate

  // controller response is immediate
  assign tcb_rdc.rdy = 1'b1;

  // there are no error cases
  assign tcb_rdc.rsp.sts = '0;

////////////////////////////////////////////////////////////////////////////////
// TCB write access
////////////////////////////////////////////////////////////////////////////////

  // write output and output enable
  always_ff @(posedge tcb_wrc.clk, posedge tcb_wrc.rst)
  if (tcb_wrc.rst) begin
    gpio_o <= '0;
    gpio_e <= '0;
  end else if (tcb_wrc.trn) begin
    // write access (write enable is not checked)
    case (tcb_wrc.req.adr[4-1:0])
      4'h0:    gpio_o <= tcb_wrc.req.wdt[GW-1:0];
      4'h4:    gpio_e <= tcb_wrc.req.wdt[GW-1:0];
      default: ;  // do nothing
    endcase
  end

  // controller response is immediate
  assign tcb_wrc.rdy = 1'b1;

  // there are no error cases
  assign tcb_wrc.rsp.sts = '0;

endmodule: tcb_ind_gpio

