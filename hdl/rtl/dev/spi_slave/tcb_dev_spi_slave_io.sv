////////////////////////////////////////////////////////////////////////////////
// TCB peripheral: SPI slave controller I/O
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

module tcb_dev_spi_slave_io #(
    parameter  int unsigned DAT = 8,    // shift register width
    parameter  bit          MOD = 1'b0  // mode 0 - single, 1 - dual
)(
    // system signals
    input  logic clk,  // clock
    input  logic rst,  // reset
    // parallel interface
    output logic           par_trn,  // data transfer pulse
    output logic [DAT-1:0] par_des,  // data from deserializer
    input  logic [DAT-1:0] par_ser,  // data to serializer
    // SPI interface
    input  logic       spi_sclk,  // serial clock
    input  logic       spi_ss_n,  // slave select
    input  logic       spi_mosi,  // master-out slave-in (sio[0])
    output logic       spi_miso,  // master-in slave-out (sio[1])
//    input  logic [1:0] spi_io_i   // IO output        {miso, mosi}
//    output logic [1:0] spi_io_o   // IO output enable {miso, mosi}
//    output logic [1:0] spi_io_e   // IO output enable {miso, mosi}
);    

    // shift counter width
    localparam int unsigned CNT = $clog2(MOD ? DAT/2 : DAT);

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // parallel signals
    logic [DAT-1:0] spi_reg;  // SPI shift register
    logic [DAT-1:0] spi_dat;  // SPI shift register input

    // FSM signals
    logic [CNT-1:0] fsm_cnt;  // bit counter
    logic           fsm_end;  // bit counter end

    // CDC
    logic [DAT-1:0] cdc_dat;  // parallel data
    logic           cdc_trn;  // parallel transfer
    logic           cdc_

////////////////////////////////////////////////////////////////////////////////
// SPI serdes
////////////////////////////////////////////////////////////////////////////////

    generate
    if (MOD == 1'b0) begin: single

        // shift register
        always_ff @(posedge spi_sclk, negedge spi_ss_n)
        if (~spi_ss_n) begin
            fsm_cnt <= '0;
            fsm_end <= 1'b0;
            spi_reg <= '0;
        end else begin

        end

        // opposite clock edge MISO
        always_ff @(negedge spi_sclk, negedge spi_ss_n)
        if (~spi_ss_n) begin
            spi_miso <= 1'b0;
        end else begin
            spi_miso <= spi_reg[7];
        end

    end: single
    else begin: dual


        // opposite clock edge MISO
        always_ff @(negedge spi_sclk, negedge spi_ss_n)
        if (~spi_ss_n) begin
            spi_io_o <= 2'b00;
        end else begin
            spi_io_o <= spi_reg[7:6];
        end

    end: dual
    endgenerate
    



endmodule: tcb_dev_spi_slave_io
