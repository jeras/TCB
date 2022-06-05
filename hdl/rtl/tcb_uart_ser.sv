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

module tcb_uart_ser #(
  int unsigned CW = 8,  // baudrate counter width
  int unsigned DW = 8,  // shifter data width
  bit      STP = 1'b1   // STOP bit
)(
  // system signals
  input  logic          clk,
  input  logic          rst,
  // configuration
  input  logic [CW-1:0] cfg_bdr,  // baudrate
  // parallel stream
  input  logic          str_vld,  // valid
  input  logic [DW-1:0] str_dat,  // data
  output logic          str_rdy,  // ready
  // serial TX output
  output logic          txd
);

// parallel stream transfer
logic          str_trn;

// baudrate counter
logic [CW-1:0] bdr_cnt;
logic          bdr_end;

// shifter bit counter
logic  [4-1:0] shf_cnt;
logic  [4-1:0] shf_end;

// shift data register
logic [DW-1:0] shf_dat;

////////////////////////////////////////////////////////////////////////////////
// parallel stream
////////////////////////////////////////////////////////////////////////////////

// parallel stream transfer
assign str_trn = str_vld & str_rdy;

// parallel stream ready
assign str_rdy = shf_end;

////////////////////////////////////////////////////////////////////////////////
// serializer
////////////////////////////////////////////////////////////////////////////////

// baudrate generator from clock
always @ (posedge clk, posedge rst)
if (rst)        bdr_cnt <= '0;
else begin
  if (str_trn)  bdr_cnt <= '0;
  else          bdr_cnt <= bdr_cnt + (~shf_end);
end

// enable signal for shifting logic
assign bdr_end = bdr_cnt == cfg_bdr;

// bit counter
always @ (posedge clk, posedge rst)
if (rst)        shf_cnt <= 4'd0;
else begin
  if (str_trn)  shf_cnt <= 4'(DW);
  else          shf_cnt <= shf_cnt - 1;
end

// end of shift sequence
assign shf_end = shf_cnt == 4'd0;

// data shift register
// without reset, to reduce ASIC area
always @(posedge clk, posedge rst)
if (rst)             shf_dat <= {DW{STP}};
else begin
  if      (str_trn)  shf_dat <= str_dat;
  else if (bdr_end)  shf_dat <= {STP, shf_dat[DW-1:1]};
end

assign txd = shf_dat[0];

endmodule: tcb_uart_ser