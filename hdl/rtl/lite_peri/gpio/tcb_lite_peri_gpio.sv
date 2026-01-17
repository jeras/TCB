////////////////////////////////////////////////////////////////////////////////
// TCB-Lite peripheral: GPIO controller
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

module tcb_lite_peri_gpio #(
    // GPIO parameters
    int unsigned GDW = 32,  // GPIO data width
    int unsigned CDC =  2,  // implement clock domain crossing stages (0 - bypass)
    // TCB parameters
    bit          CFG_RSP_REG = 1'b1,  // register response path (by default the response is registered giving a CFG.HSK.DLY of 1)
    bit          CFG_RSP_MIN = 1'b0   // minimalistic response implementation
)(
    // GPIO signals
    output logic [GW-1:0] gpio_o,
    output logic [GW-1:0] gpio_e,
    input  logic [GW-1:0] gpio_i,
    // TCB interface
    tcb_lite_if.sub sub
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    initial begin
        assert (sub.DLY ==  0) else $error("unsupported CFG.HSK.DLY = %0d", sub.DLY);
        assert (sub.DAT >= GW) else $error("unsupported (CFG.BUS.DAT = %0d) < (GW = %0d)", sub.DAT, GW);
    end

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// GPIO instance
////////////////////////////////////////////////////////////////////////////////

    tcb_peri_gpio #(
        // GPIO parameters
        .GW           (GDW),
        .CFG_CDC      (CDC),
        // system interface parameters
        .DAT          (sub.DAT),
        .CFG_RSP_REG  (CFG_RSP_REG),
        .CFG_RSP_MIN  (CFG_RSP_MIN)
    ) gpio (
        // GPIO signals
        .gpio_o  (gpio_o),
        .gpio_e  (gpio_e),
        .gpio_i  (gpio_i),
        // system signals
        .clk  (sub.clk),
        .rst  (sub.rst),
        // system write interface
        .wen  (sub.req.wen & sub.trn),
        .wad  (sub.req.adr),
        .wdt  (sub.req.wdt),
        // system read interface
        .ren  (~sub.req.wen & sub.trn),
        .rad  (sub.req.adr),
        .rdt  (sub.rsp.rdt)
    );

    // status response
    assign sub.rsp.sts =   '0;
    assign sub.rsp.err = 1'b0;

endmodule: tcb_lite_peri_gpio
