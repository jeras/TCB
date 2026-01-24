////////////////////////////////////////////////////////////////////////////////
// TCB peripheral: GPIO controller: generic CDC implementation for inference
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

module tcb_peri_gpio_cdc #(
    // GPIO parameters
    parameter  int unsigned DAT =   32,  // GPIO data width
    parameter  int unsigned CDC =    2,  // implement clock domain crossing stages (0 - bypass)
    parameter  bit          IEN = 1'b1   // implement input enable mask (to minimize toggling propagation)
)(
    // system signals
    input  logic           clk,  // clock
    input  logic           rst,  // reset
    // GPIO signals
    input  logic [DAT-1:0] gpio_i,  // GPIO input data
    input  logic [DAT-1:0] gpio_e,  // GPIO input enable
    output logic [DAT-1:0] gpio_r   // GPIO registered/synchronized output
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    initial
    begin
        assert (CDC >= 2) else $error("CDC depth must be at least 2.");
        assert (IEN == 1'b0) else $warning("Input enable might not synthesize properly on FPGA.");
    end

////////////////////////////////////////////////////////////////////////////////
// GPIO input CDC (clock domain crossing)
////////////////////////////////////////////////////////////////////////////////

    // temporary signal for synchronization
    logic [DAT-1:0] gpio_t [CDC-1:0];

    // asynchronous input synchronization
    always_ff @(posedge clk, posedge rst)
    if (rst) begin
        gpio_t <= '{default: '0};
    end else begin
        gpio_t[      0] <= gpio_i & gpio_e;
        gpio_t[CDC-1:1] <= gpio_t[CDC-2:0];
    end

    assign gpio_r = gpio_t[CDC-1];

endmodule: tcb_peri_gpio_cdc
