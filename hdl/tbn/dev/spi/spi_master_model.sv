////////////////////////////////////////////////////////////////////////////////
// SPI master model
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

module spi_master_model
    import spi_pkg::*;
#(
    // shift register width
    parameter  int unsigned DAT = 8,
    // IO data width (supported values are 2, 4, 8)
    parameter  int unsigned IO_WIDTH = 2
    // default clock period
    parameter  realtime     PERIOD = 20ns,  // 50MHz
)(
    inout  wire                sclk,  // serial clock
    output wire                ss_n,  // slave select
    inout  wire [IO_WIDTH-1:0] sdio   // serial data I/O {sdio[IO_WIDTH-1:2], miso, mosi}
);

////////////////////////////////////////////////////////////////////////////////
// local configuration accessible from outside
////////////////////////////////////////////////////////////////////////////////

    // clock period (initialized with parameter)
    realtime cfg_period = PERIOD;

    // SPI mode
    spi_mode_t cfg_mode = SPI_MODE0;

    // SPI width (single, dual, quad, octa)
    spi_size_e cfg_size = SPI_SINGLE;

    // SPI duplex (half, dual)
    spi_duplex_e cfg_duplex = SPI_FULL;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    logic                spi_clk;  // clock
    logic                spi_sel;  // select
    logic                spi_oen;  // output enable
    logic [IO_WIDTH-1:0] spi_sdi;  // serial data input
    logic [IO_WIDTH-1:0] spi_sdo;  // serial data output

////////////////////////////////////////////////////////////////////////////////
// initialization
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// SPI transfer
////////////////////////////////////////////////////////////////////////////////

    task spi_transfer (
        input  logic [DAT-1:0] dto,  // output data
        output logic [DAT-1:0] dti,  // input  data
        output logic [DAT-1:0] oen,  // output enable
        input  bit             lst,  // last (closes chip select window)
    );
        // start transfer
        spi_sel <= 1'b1;
        spi_oen <= oen;
        // ser/des data
        for (int unsigned i=0; i<DAT; i++) begin
            spi_clk <= cfg_mode.cpha;
            spi_sdo[0+:2**cfg_size] <= dto[8-1-i-:2**cfg_size];
            #(cfg_period/2);
            spi_clk <= ~cfg_mode.cpha;
            dti[8-1-i-:2**cfg_size] <= spi_sdi;
            #(cfg_period/2);
        end;
        // set clock back to idle state
        spi_clk = cfg_mode.cpol;
        // end transfer
        if (lst) begin
            spi_sel <= 1'b0;
            spi_oen <= 1'b0;
        end
    endtask: spi_transfer

////////////////////////////////////////////////////////////////////////////////
// SPI I/O tristate drivers
////////////////////////////////////////////////////////////////////////////////

    // serial clock
    assign sclk = spi_clk;
    // slave select (active low)
    assign ss_n = spi_sel;
    // serial data I/O
    assign sdio[0] = {cfg_duplex == SPI_FULL} ? spi_sdo[0] : (spi_oen ? spi_sdo[0] : 1'bz);  // MOSI
    assign sdio[1] = {cfg_duplex == SPI_FULL} ? 1'bz       : (spi_oen ? spi_sdo[1] : 1'bz);  // MISO
    assign sdio[IO_WIDTH-1:2] = (spi_oen ? spi_sdo[IO_WIDTH-1:2] : 'z);

endmodule: spi_master_model
