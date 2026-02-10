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
    parameter  int unsigned DAT = 8  // shift register width
)(
    // system signals
    input  logic clk,  // clock
    input  logic rst,  // reset
    // configuration
    input  logic           cfg_mod,  // mode 0 - single, 1 - dual
    // parallel request/response interface
    output logic           par_stb,  // data strobe
    output logic [DAT-1:0] par_req,  // request
    input  logic           par_dir,  // direction (0 - request, 1 - response)
    input  logic [DAT-1:0] par_rsp,  // response
    // SPI interface
    input  logic       spi_sclk,  // serial clock
    input  logic       spi_ss_n,  // slave select
    input  logic [1:0] spi_io_i,  // IO output        {miso, mosi}
    output logic [1:0] spi_io_o,  // IO output enable {miso, mosi}
    output logic [1:0] spi_io_e   // IO output enable {miso, mosi}
);    

    // shift counter width
    localparam int unsigned CNT = $clog2(DAT);

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // SPI domain parallel signals
    logic [DAT-1:0] spi_reg;  // SPI shift register
    logic [DAT-1:0] spi_wdt;  // write data
    logic [DAT-1:0] spi_rdt;  // read data buffer
    logic           spi_dir;  // SPI I/O direction (0 - inputs, 1 - outputs)

    // FSM signals
    logic [CNT-1:0] fsm_cnt;  // bit counter
    logic           fsm_end;  // bit counter end
    logic           fsm_tgl;  

    // CDC signals
    logic   [3-1:0] cdc_dly;  
    logic           cdc_tgl;

////////////////////////////////////////////////////////////////////////////////
// SPI ser/des
////////////////////////////////////////////////////////////////////////////////

    // shift register
    always_ff @(posedge spi_sclk, negedge spi_ss_n)
    if (~spi_ss_n) begin
        fsm_cnt <= CNT'(0);
        spi_reg <= '0;
        spi_dir <= 1'b0;
    end else begin
        // increment bit counter
        fsm_cnt <= fsm_cnt + CNT'(cfg_mod ? 2 : 1);
        // shift register
        if (fsm_end) begin
            // parallel load
            spi_reg <= par_rsp;
            spi_dir <= par_dir;
        end else begin
            // shift
            spi_reg <= spi_wdt;
        end
    end

    // shift counter reaches end
    // MSB first concatenation with MOSI
    // SPI I/O output driver enable
    always_comb
    case (cfg_mod)
        // single bit mode
        1'b0: begin
            fsm_end = (fsm_cnt == DAT-1);
            spi_wdt = {spi_reg, spi_io_i[0]}[DAT-1:0];
            spi_io_e = 2'b10;  // {miso, mosi}
        end
        // dual bit mode
        1'b1: begin
            fsm_end = (fsm_cnt == DAT-2);
            spi_wdt = {spi_reg, spi_io_i[1:0]}[DAT-1:0];
            spi_io_e = 
        end
    endcase
    
    // opposite clock edge MISO
    always_ff @(negedge spi_sclk, negedge spi_ss_n)
    if (~spi_ss_n) begin
        spi_io_o <= 2'b00;
    end else begin
        spi_io_o <= spi_reg[7:6];
    end

    // SPI shift register parallel read data buffer
    always_ff @(posedge spi_sclk)
    if (fsm_end)  spi_rdt <= spi_wdt;

    // SPI toggler
    // reset on parallel clock domain
    // toggle on every received byte
    always_ff @(negedge spi_sclk, negedge rst)
    if (rst) begin
        fsm_tgl <= 1'b0;
    end else begin
        if (fsm_end)  fsm_tgl <= ~fsm_tgl;
    end

////////////////////////////////////////////////////////////////////////////////
// parallel clock domain crossing
////////////////////////////////////////////////////////////////////////////////

    // toggling signal delay line in parallel clock domain
    always_ff @(negedge clk, negedge rst)
    if (rst) begin
        cdc_dly <= 3'b000;
        par_stb <= 1'b0;
    end else begin
        cdc_dly <= {cdc_dly, fsm_tgl}[3-1:0];
        par_stb <= cdc_tgl;
    end

    // parallel data transfer on delayed toggle signal
    assign cdc_tgl = ^cdc_dly[2:1];

    // parallel request data is read data form SPI shift register
    always_ff @(negedge clk, negedge rst)
    if (cdc_tgl)  par_req <= spi_rdt;

endmodule: tcb_dev_spi_slave_io
