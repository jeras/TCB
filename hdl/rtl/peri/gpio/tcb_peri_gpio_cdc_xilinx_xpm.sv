////////////////////////////////////////////////////////////////////////////////
// TCB peripheral: GPIO controller: CDC implementation using Xilinx XPM library
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
    input  logic [DAT-1:0] gpio_i,  // data input
    input  logic [DAT-1:0] gpio_e,  // enable input (not used)
    output logic [DAT-1:0] gpio_r   // resynchronized output
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    initial
    begin
        assert (CDC >= 2) else $error("Xilinx XPM CDC depth must be at least 2.");
        assert (IEN == 1'b0) else $error("Xilinx CDC and input buffers do not support input enable.");
    end

////////////////////////////////////////////////////////////////////////////////
// GPIO input CDC (clock domain crossing)
////////////////////////////////////////////////////////////////////////////////

    // xpm_cdc_array_single: Single-bit Array Synchronizer
    // Xilinx Parameterized Macro, version 2021.2
    xpm_cdc_array_single #(
        .DEST_SYNC_FF   (CDC),  // DECIMAL; range: 2-10
        .INIT_SYNC_FF   (0),    // DECIMAL; 0=disable simulation init values, 1=enable simulation init values
        .SIM_ASSERT_CHK (0),    // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
        .SRC_INPUT_REG  (0),    // DECIMAL; 0=do not register input, 1=register input
        .WIDTH          (DAT)   // DECIMAL; range: 1-1024
    ) gpio_cdc (
        .src_clk  (clk),
        .src_in   (gpio_i),
        .dest_clk (clk),
        .dest_out (gpio_r)
    );

endmodule: tcb_peri_gpio_cdc
