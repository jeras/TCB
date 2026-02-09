////////////////////////////////////////////////////////////////////////////////
// TCB-Lite interface device: SPI slave controller
////////////////////////////////////////////////////////////////////////////////
// Copyright 2025 Iztok Jeras
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

module tcb_lite_dev_spi_slave
    import tcb_lite_pkg::*;
#(
    // protocol parameters
    parameter  int unsigned ADR = 22  // 6+16 = 22 bit address 
)(
    // SPI interface
    input  logic spi_sclk,  // serial clock
    input  logic spi_ss_n,  // slave select
    input  logic spi_mosi,  // master-out slave-in
    output logic spi_miso,  // master-in slave-out
    // TCB interface
    tcb_lite_if.man man,
    // IRQ interface
    output logic irq
);



endmodule: tcb_lite_dev_spi_slave
