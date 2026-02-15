////////////////////////////////////////////////////////////////////////////////
// SPI model testbench
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

module spi_model_tb
    import spi_pkg::*;
#(
    // shift register width
    parameter  int unsigned DAT = 8,
    // IO data width (supported values are 2, 4, 8)
    parameter  int unsigned IO_WIDTH = 2
);

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    wire                sclk;  // serial clock
    wire                ss_n;  // slave select
    wire [IO_WIDTH-1:0] sdio;  // serial data I/O {sdio[IO_WIDTH-1:2], miso, mosi}

////////////////////////////////////////////////////////////////////////////////
// SPI master/slave model instances
////////////////////////////////////////////////////////////////////////////////

    // SPI master model
    spi_master_model #(
        // shift register width
        .DAT  (DAT),
        // IO data width (supported values are 2, 4, 8)
        .IO_WIDTH (IO_WIDTH)
    //    // default transfer configuration
    //    .CFG_WIDTH  (CFG_WIDTH ),
    //    .CFG_DUPLEX (CFG_DUPLEX),
    //    .CFG_MODE   (CFG_MODE  ),
    //    // default timing
    //    .CFG_PERIOD (CFG_PERIOD),
    //    .CFG_SETUP  (CFG_SETUP ),
    //    .CFG_HOLD   (CFG_HOLD  ),
    //    .CFG_OUTPUT (CFG_OUTPUT),
    //    .CFG_ENABLE (CFG_ENABLE),
    ) master (
        .sclk  (sclk),
        .ss_n  (ss_n),
        .sdio  (sdio) 
    );

    // SPI slave model
    spi_slave_model #(
        // shift register width
        .DAT  (DAT),
        // IO data width (supported values are 2, 4, 8)
        .IO_WIDTH (IO_WIDTH)
    //    // default transfer configuration
    //    .CFG_WIDTH  (CFG_WIDTH ),
    //    .CFG_DUPLEX (CFG_DUPLEX),
    //    .CFG_MODE   (CFG_MODE  ),
    //    // default timing
    //    .CFG_PERIOD (CFG_PERIOD),
    //    .CFG_SETUP  (CFG_SETUP ),
    //    .CFG_HOLD   (CFG_HOLD  ),
    //    .CFG_OUTPUT (CFG_OUTPUT),
    //    .CFG_ENABLE (CFG_ENABLE),
    ) slave (
        .sclk  (sclk),
        .ss_n  (ss_n),
        .sdio  (sdio) 
    );

////////////////////////////////////////////////////////////////////////////////
// test sequence
////////////////////////////////////////////////////////////////////////////////

    initial begin
        logic [DAT-1:0] data_mosi;
        logic [DAT-1:0] data_miso;

        data_mosi = 8'h5a;
        master.spi_transfer(data_mosi, data_miso);
    end

endmodule: spi_model_tb
