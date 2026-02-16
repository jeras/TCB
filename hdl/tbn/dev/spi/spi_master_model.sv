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
    parameter  int unsigned IOW = 2,
    // default transfer configuration
    parameter  spi_width_e  CFG_WIDTH  = SPI_SINGLE,
    parameter  spi_duplex_e CFG_DUPLEX = SPI_FULL,
    parameter  spi_mode_t   CFG_MODE   = SPI_MODE0,
    // default timing
    parameter  realtime     CFG_PERIOD = 20ns,  // 50MHz
    parameter  realtime     CFG_SETUP  = 0ns,
    parameter  realtime     CFG_HOLD   = 0ns,
    parameter  realtime     CFG_OUTPUT = 0ns,
    parameter  realtime     CFG_ENABLE = 0ns
)(
    output wire           sclk,  // serial clock
    output wire           ss_n,  // slave select
    inout  wire [IOW-1:0] sdio   // serial data I/O {sdio[IOW-1:2], miso, mosi}
);

////////////////////////////////////////////////////////////////////////////////
// local configuration accessible from outside
////////////////////////////////////////////////////////////////////////////////

    // clock period (initialized with parameter)
    realtime cfg_period = CFG_PERIOD;

    // SPI mode
    spi_mode_t cfg_mode = SPI_MODE0;

////////////////////////////////////////////////////////////////////////////////
// port drivers
////////////////////////////////////////////////////////////////////////////////

    logic           sclk_o;
    logic           ss_n_o;
    logic [IOW-1:0] sdio_o;
    logic [IOW-1:0] sdio_e;

    assign sclk = sclk_o;
    assign ss_n = ss_n_o;
    generate
    for (genvar i=0; i<IOW; i++) begin
        assign sdio[i] = sdio_e[i] ? sdio_o[i] : 1'bz;
    end
    endgenerate
    

////////////////////////////////////////////////////////////////////////////////
// initialization
////////////////////////////////////////////////////////////////////////////////

    initial
    begin
        // idle
        sclk_o = cfg_mode.cpol;
        ss_n_o = 1'b1;
        sdio_o = 'x;
        sdio_e = '0;
    end

////////////////////////////////////////////////////////////////////////////////
// SPI transfer
////////////////////////////////////////////////////////////////////////////////

    task automatic spi_transfer (
        input  logic [DAT-1:0] data_o,               // output data
        output logic [DAT-1:0] data_i,               // input  data
        input  bit             last   = 1'b1,        // last (closes chip select window)
        input  bit             enable = 1'b1,        // output enable
        input  spi_duplex_e    duplex = SPI_HALF,    // I/O duplex (half, full)
        input  spi_width_e     width  = SPI_SINGLE,  // I/O width (single, dual, quad, octa)
        input  realtime        period = cfg_period   // clock period
    );
        // start transfer
        sclk_o = cfg_mode.cpol;
        ss_n_o = 1'b0;
        case ({duplex, width})
            {SPI_FULL, SPI_SINGLE}: sdio_e = '{0: enable, 1: 1'b0  ,                       default: 1'b0};
            {SPI_HALF, SPI_SINGLE}: sdio_e = '{0: enable,                                  default: 1'b0};
            {SPI_HALF, SPI_DUAL  }: sdio_e = '{0: enable, 1: enable,                       default: 1'b0};
            {SPI_HALF, SPI_QUAD  }: sdio_e = '{0: enable, 1: enable, 2: enable, 3: enable, default: 1'b0};
            {SPI_HALF, SPI_OCTA  }: sdio_e = '{                                            default: enable};
        endcase
        sdio_e = '1;
        // ser/des data
        for (int unsigned i=0; i<DAT; i+=2**width) begin
            // data output
            sclk_o = cfg_mode.cpha;
            for (int unsigned j=0; j<IOW; j++) begin
                sdio_o[j] = data_o[8-1-(i+j)];
            end
            #(period/2);
            // data input
            sclk_o = ~cfg_mode.cpha;
            for (int unsigned j=0; j<IOW; j++) begin
            data_o[8-1-(i+j)] = sdio[j];
            end
            #(period/2);
        end;
        // set clock back to idle state
        sclk_o = cfg_mode.cpol;
        // end transfer
        if (last) begin
            ss_n_o = 1'b1;
            sdio_e = '0;
        end
    endtask: spi_transfer

////////////////////////////////////////////////////////////////////////////////
// SPI transaction
////////////////////////////////////////////////////////////////////////////////

    task automatic spi_transaction (
        input  logic [DAT-1:0] data_o [],                           // output data
        output logic [DAT-1:0] data_i [],                           // input  data
        input  logic           enable [] = '{default: 1'b1},        // output enable
        input  spi_duplex_e    duplex [] = '{default: SPI_HALF},    // I/O duplex (half, full)
        input  spi_width_e     width  [] = '{default: SPI_SINGLE},  // I/O width (single, dual, quad, octa)
        input  realtime        period [] = '{default: cfg_period}   // clock period
    );
        int unsigned size = data_o.size();
        data_i = new[size];
        for (int unsigned i=0; i<size; i++) begin
            spi_transfer(
                .data_o (data_o[i]),
                .data_i (data_i[i]),
                .last   (i!=size-1),
                .enable (enable[i<enable.size() ? i : enable.size()]),
                .duplex (duplex[i<duplex.size() ? i : duplex.size()]),
                .width  (width [i<width .size() ? i : width .size()]),
                .period (period[i<period.size() ? i : period.size()])
            );
        end
    endtask: spi_transaction

endmodule: spi_master_model
