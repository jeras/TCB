////////////////////////////////////////////////////////////////////////////////
// TCB-Lite interface peripheral: GPIO controller
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

module tcb_lite_peri_gpio
    import tcb_lite_pkg::*;
#(
    // GPIO parameters
    parameter  int unsigned GPIO_DAT = 32,  // GPIO data width
    parameter  int unsigned GPIO_CDC =  2,  // implement clock domain crossing stages (0 - bypass)
    // optional implementation configuration
    parameter  bit                SYS_IEN =   '0,  // input enable implementation
    parameter  bit [GPIO_DAT-1:0] SYS_IRQ =   '1,  // interrupt request implementation mask
    parameter  bit                SYS_MIN = 1'b0   // minimalistic response implementation (configuration is write only)
    // NOTE 1: if none of the interrupts are enabled, the controller has a smaller address space
)(
    // GPIO signals
    output logic [GPIO_DAT-1:0] gpio_o,
    output logic [GPIO_DAT-1:0] gpio_e,
    input  logic [GPIO_DAT-1:0] gpio_i,
    // TCB interface
    tcb_lite_if.sub sub,
    // IRQ interface
    output logic irq
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    initial begin
        assert (sub.DLY ==        0) else $error("Unsupported DLY = %0d (must be 0)", sub.DLY);
        assert (sub.DAT >= GPIO_DAT) else $error("Unsupported (DAT = %0d) < (GPIO_DAT = %0d)", sub.DAT, GPIO_DAT);
    end

////////////////////////////////////////////////////////////////////////////////
// GPIO instance
////////////////////////////////////////////////////////////////////////////////

    logic [3-1:0] sys_req_adr;

    // check whether at least one GPIO pin has enabled interrupt support
    generate
    if (~|SYS_IRQ) begin
        assign sys_req_adr =        sub.req.adr[sub.MAX+:3];
    end else begin
        assign sys_req_adr = {1'b0, sub.req.adr[sub.MAX+:2]};
    end
    endgenerate

    // TCB variant independent instance
    tcb_peri_gpio #(
        // GPIO parameters
        .GPIO_DAT (GPIO_DAT),
        .GPIO_CDC (GPIO_CDC),
        // system interface parameters
        .SYS_DAT  (sub.DAT),
        // optional implementation configuration
        .SYS_IEN  (SYS_IEN),
        .SYS_IRQ  (SYS_IRQ),
        .SYS_MIN  (SYS_MIN)
    ) gpio (
        // GPIO signals
        .gpio_o   (gpio_o),
        .gpio_e   (gpio_e),
        .gpio_i   (gpio_i),
        // system signals
        .clk      (sub.clk),
        .rst      (sub.rst),
        // system write interface
        .sys_wen  (sub.req.wen & sub.trn),
        .sys_wad  (sys_req_adr),
        .sys_wdt  (sub.req.wdt),
        // system read interface
        .sys_ren  (~sub.req.wen & sub.trn),
        .sys_rad  (sys_req_adr),
        .sys_rdt  (sub.rsp.rdt),
        // interrupt request interface
        .irq      (irq)
    );

    // TCB status response
    assign sub.rsp.sts =   '0;
    assign sub.rsp.err = 1'b0;

    // TCB backpressure
    assign sub.rdy = 1'b1;

endmodule: tcb_lite_peri_gpio
