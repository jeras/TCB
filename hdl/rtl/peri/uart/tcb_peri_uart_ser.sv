////////////////////////////////////////////////////////////////////////////////
// TCB interface UART controller, asynchronous serializer
////////////////////////////////////////////////////////////////////////////////
// Copyright 2022 Iztok Jeras
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

module tcb_peri_uart_ser #(
    int unsigned RW = 8,  // baudrate number width
    int unsigned DW = 8,  // shifter data width
    int unsigned SW = 1   // stop sequence width
)(  
    // system signals
    input  logic          clk,
    input  logic          rst,
    // configuration
    input  logic [RW-1:0] cfg_bdr,  // baudrate
    // parallel stream
    input  logic          str_vld,  // valid
    input  logic [DW-1:0] str_dat,  // data
    output logic          str_rdy,  // ready
    // serial TX output
    output logic          txd
);

    // shift sequence length (start + data + stop)
    localparam int unsigned SL = 1 + DW + SW;

    // parallel stream transfer
    logic          str_trn;

    // baudrate counter
    logic [RW-1:0] bdr_cnt;
    logic          bdr_end;

    // shifter bit counter and run status
    logic  [4-1:0] shf_cnt;
    logic          shf_end;
    logic          shf_run;

    // shift data register
    logic [DW+1-1:0] shf_dat;

////////////////////////////////////////////////////////////////////////////////
// parallel stream
////////////////////////////////////////////////////////////////////////////////

    // parallel stream transfer
    assign str_trn = str_vld & str_rdy;

    // parallel stream ready
    assign str_rdy = ~shf_run | (shf_end & bdr_end);

////////////////////////////////////////////////////////////////////////////////
// serializer
////////////////////////////////////////////////////////////////////////////////

    // baudrate generator from clock
    always_ff @(posedge clk, posedge rst)
    if (rst)               bdr_cnt <= '0;
    else begin
        if      (str_trn)  bdr_cnt <= '0;
        else if (shf_run)  bdr_cnt <= bdr_end ? '0 : bdr_cnt + 1;
    end

    // enable signal for shifting logic
    assign bdr_end = bdr_cnt == cfg_bdr;

    // bit counter
    always_ff @(posedge clk, posedge rst)
    if (rst) begin
        shf_cnt <= 4'd0;
        shf_run <= 1'b0;
    end else begin
        if (str_trn) begin
            shf_cnt <= 4'd0;
            shf_run <= 1'b1;
        end else begin
            if (shf_run & bdr_end) begin
                if (shf_end) begin
                    shf_run <= 1'b0;
                    shf_cnt <= 4'd0;
                end else begin
                    shf_cnt <= shf_cnt + 1;
                end
            end
        end
    end

    // end of shift sequence
    assign shf_end = shf_cnt == 4'(SL-1);

    // data shift register
    // without reset, to reduce ASIC area
    always_ff @(posedge clk, posedge rst)
    if (rst)                shf_dat <= '1;
    else begin
        if       (str_trn)  shf_dat <= {      str_dat        , 1'b0};
        else if  (bdr_end)  shf_dat <= {1'b1, shf_dat[DW-0:1]      };
    end

    assign txd = shf_dat[0];

endmodule: tcb_peri_uart_ser