////////////////////////////////////////////////////////////////////////////////
// TCB peripheral: GPIO controller
//
// NOTE: In case this module is connected to asynchronous signals,
//       the input signals `gpio_i` require a CDC synchronizer.
//       By default a 2 FF synchronizer is implemented by the SYS_CDC parameter.
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
    localparam int unsigned  SYS_ADR = 3,
    parameter  int unsigned  SYS_DAT = 32,
    // optional implementation configuration
    parameter  bit           SYS_IEN =   '0,  // input enable implementation
    parameter  bit [GDW-1:0] SYS_IRQ =   '1,  // interrupt request implementation mask
    parameter  bit           SYS_MIN = 1'b0   // minimalistic response implementation (configuration is write only)
    // NOTE 1: if none of the interrupts are enabled, the controller has a smaller address space
)(
    // GPIO signals
    output logic [GDW-1:0] gpio_o,
    output logic [GDW-1:0] gpio_e,
    input  logic [GDW-1:0] gpio_i,
    // system signals
    input  logic               clk,  // clock
    input  logic               rst,  // reset
    // system bus write interface
    input  logic               sys_wen,  // write enable
    input  logic [SYS_ADR-1:0] sys_wad,  // write address
    input  logic [SYS_DAT-1:0] sys_wdt,  // write data
    // system bus read interface
    input  logic               sys_ren,  // read enable
    input  logic [SYS_ADR-1:0] sys_rad,  // read address
    output logic [SYS_DAT-1:0] sys_rdt,  // read data
    // interrupt request interface
    output logic               irq
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    initial begin
        assert (SYS_DAT >= GDW) else $error("More GPIO signals (GDW=%0d) than system bus data width (SYS_DAT=%0d).", GDW, SYS_DAT);
    end

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // GPIO data registers
    // TODO: using GDW would make more sense
    logic [GDW-1:0] gpio_oe;  // output enable
    logic [GDW-1:0] gpio_od;  // output data
    logic [GDW-1:0] gpio_ie;  // input enable
    logic [GDW-1:0] gpio_id;  // input data

    // GPIO interrupt registers
    logic [GDW-1:0] irq_ena;  // interrupt enable
    logic [GDW-1:0] irq_mod;  // mode (0-value, 1-edge pulse)
    logic [GDW-1:0] irq_pol;  // value/edge polarity (0-low/falling, 1-high/rising);

    // GPIO interrupt signals
    logic [GDW-1:0] irq_val;  // interrupt value input
    logic [GDW-1:0] irq_dly;  // interrupt delay register
    logic [GDW-1:0] irq_edg;  // interrupt edge detection status
    logic [GDW-1:0] irq_sts;  // interrupt status
    logic [GDW-1:0] irq_clr;  // interrupt clear

////////////////////////////////////////////////////////////////////////////////
// GPIO output drivers
////////////////////////////////////////////////////////////////////////////////

    assign gpio_o = gpio_od;  // output data   register cast to GPIO out
    assign gpio_e = gpio_oe;  // output enable register cast to GPIO ena

////////////////////////////////////////////////////////////////////////////////
// GPIO input CDC (clock domain crossing)
////////////////////////////////////////////////////////////////////////////////

    // read value
    logic [GDW-1:0] gpio_r;

    generate
    if (CDC > 1) begin: gen_cdc_stages

        tcb_peri_gpio_cdc #(
            .GDW (GDW),
            .CDC (CDC),
            .IEN (SYS_IEN)
        ) cdc (
            .gpio_i  (gpio_i),
            .gpio_e  (gpio_e),
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
    assign gpio_id = gpio_ie & gpio_r;

////////////////////////////////////////////////////////////////////////////////
// interrupt logic
////////////////////////////////////////////////////////////////////////////////

    // synchronized GPIO inputs are used as input value into interrupt logic
    // NOTE: interrupt enable is used early to minimize power
    assign irq_val = (gpio_r ^ irq_pol) & irq_ena;

    // input values are delayed (only the ones in edge mode, to save power)
    always_ff @(posedge clk, posedge rst)
    if (rst)  irq_dly <= '0;
    else      irq_dly <= irq_ena & irq_mod;

    // edge detection registers
    always_ff @(posedge clk, posedge rst)
    if (rst)  irq_dly <= '0;
    else      irq_edg <= (irq_val ^ irq_dly) & ~irq_clr;

    // either a level or pulse
    assign irq_sts = (irq_val & ~irq_mod) | (irq_edg & irq_mod);

    // unary OR of interrupt status masked by interrupt enable (both programmable and parameter)
    assign irq = |(irq_sts & SYS_IRQ);

////////////////////////////////////////////////////////////////////////////////
// system read access
////////////////////////////////////////////////////////////////////////////////

    // read access
    always_comb
    case (sys_rad)
        3'd0: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(gpio_oe);  // GPIO output enable
        3'd1: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(gpio_od);  // GPIO output data
        3'd2: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(gpio_ie);  // GPIO input enable
        3'd3: sys_rdt =                SYS_DAT'(gpio_id);  // GPIO input data
        3'd4: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(irq_ena);  // IRQ enable
        3'd5: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(irq_mod);  // IRQ mode
        3'd6: sys_rdt = SYS_MIN ? 'x : SYS_DAT'(irq_pol);  // IRQ polarity
        3'd7: sys_rdt =                SYS_DAT'(irq_sts);  // IRQ status
    endcase

////////////////////////////////////////////////////////////////////////////////
// TCB write access
////////////////////////////////////////////////////////////////////////////////

    // write output and output enable
    always_ff @(posedge clk, posedge rst)
    if (rst) begin
        gpio_oe <= '0;
        gpio_od <= '0;
        gpio_ie <= '0;
        irq_ena <= '0;
        irq_mod <= '0;
        irq_pol <= '0;
    end else begin
        if (sys_wen) begin
            // write access
            case (sys_wad)
                3'h0: gpio_oe <= GDW'(sys_wdt);
                3'h1: gpio_od <= GDW'(sys_wdt);
                3'h2: gpio_ie <= GDW'(sys_wdt);
            //  3'h3
                3'd4: irq_ena <= GDW'(sys_wdt);
                3'd5: irq_mod <= GDW'(sys_wdt);
                3'd6: irq_pol <= GDW'(sys_wdt);
            //  3'd7:
                default: ;  // do nothing
            endcase
        end
    end

    // interrupt clear pulse on write to interrupt status register
    assign irq_clr = (sys_wen & (sys_wad == 3'd7)) ? GDW'(sys_wdt) : '0;

endmodule: tcb_peri_gpio
