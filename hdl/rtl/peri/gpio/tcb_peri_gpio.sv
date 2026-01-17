////////////////////////////////////////////////////////////////////////////////
// TCB peripheral: GPIO controller
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

module tcb_peri_gpio #(
    // GPIO parameters
    parameter  int unsigned GDW = 32,  // GPIO data width
    parameter  int unsigned CDC =  2,  // implement clock domain crossing stages (0 - bypass)
    // system interface parameters
    localparam int unsigned ADR = 2,
    parameter  int unsigned DAT = 32,
    parameter  bit          CFG_RSP_REG = 1'b1,  // register response path (by default the response is registered giving a CFG.HSK.DLY of 1)
    parameter  bit          CFG_RSP_MIN = 1'b0   // minimalistic response implementation
)(
    // GPIO signals
    output logic [GDW-1:0] gpio_o,
    output logic [GDW-1:0] gpio_e,
    input  logic [GDW-1:0] gpio_i,
    // system signals
    input  logic           clk,  // clock
    input  logic           rst,  // reset
    // system write interface
    input  logic           wen,  // write enable
    input  logic [ADR-1:0] wad,  // write address
    input  logic [DAT-1:0] wdt,  // write data
    // system read interface
    input  logic           ren,  // read enable
    input  logic [ADR-1:0] rad,  // read address
    output logic [DAT-1:0] rdt   // read data
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    initial begin
        assert (DAT >= GDW) else $error("More GPIO signals (GDW=%0d) than system bus data width (DAT=%0d).", GDW, DAT);
    end

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // GPIO registers
    logic [DAT-1:0] gpio_oe;
    logic [DAT-1:0] gpio_od;
    logic [DAT-1:0] gpio_ie;
    logic [DAT-1:0] gpio_id;

////////////////////////////////////////////////////////////////////////////////
// GPIO output drivers
////////////////////////////////////////////////////////////////////////////////

    assign gpio_o = GDW'(gpio_od);  // output data   register cast to GPIO out
    assign gpio_e = GDW'(gpio_oe);  // output enable register cast to GPIO ena

////////////////////////////////////////////////////////////////////////////////
// GPIO input CDC (clock domain crossing)
////////////////////////////////////////////////////////////////////////////////

    // read value
    logic [GDW-1:0] gpio_r;

    generate
    if (CDC > 1) begin: gen_cdc_stages

        tcb_peri_gpio_cdc #(
            .GDW (GDW),
            .CDC (CDC)
        ) cdc (
            .gpio_i  (gpio_i),
            .gpio_r  (gpio_r)
        );

    end: gen_cdc_stages
    else if (CDC == 1) begin: gen_cdc_error

        initial $error("GPIO CDC of a single stage is not supported.");

    end: gen_cdc_error
    else begin: gen_cdc_bypass

        // bypass CDC code
        assign gpio_r = gpio_i;

        // NOTE: the assumption is, it is done externally
        initial $warning("GPIO CDC bypass, assuming it is done externally.");

    end: gen_cdc_bypass
    endgenerate

    // system access mapping
    assign gpio_id = gpio_ie & DAT'(gpio_r);

////////////////////////////////////////////////////////////////////////////////
// system read access
////////////////////////////////////////////////////////////////////////////////

    // read access
    generate
    // minimalistic implementation
    if (CFG_RSP_MIN) begin: gen_rsp_min

        // only the GPIO input can be read
        assign rdt = gpio_id;

    end: gen_rsp_min
    // normal implementation
    else begin: gen_rsp_nrm

        // GPIO output/input enable/data are decoded
        always_comb
        case (rad)
            2'd0:    rdt = gpio_oe;  // output enable
            2'd1:    rdt = gpio_od;  // output data
            2'd2:    rdt = gpio_ie;  // input enable
            default: rdt = gpio_id;  // input data
        endcase

    end: gen_rsp_nrm
    endgenerate

////////////////////////////////////////////////////////////////////////////////
// TCB write access
////////////////////////////////////////////////////////////////////////////////

    // write output and output enable
    always_ff @(posedge clk, posedge rst)
    if (rst) begin
        gpio_o <= '0;
        gpio_e <= '0;
    end else if (wen) begin
        // write access
        case (rad)
            2'h0:    gpio_oe <= wdt[GDW-1:0];
            2'h1:    gpio_od <= wdt[GDW-1:0];
            2'h2:    gpio_ie <= wdt[GDW-1:0];
            default: ;  // do nothing
        endcase
    end

endmodule: tcb_peri_gpio
