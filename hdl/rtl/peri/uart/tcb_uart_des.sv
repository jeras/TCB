////////////////////////////////////////////////////////////////////////////////
// TCB interface UART controller, asynchronous deserializer
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

module tcb_uart_des #(
  int unsigned RW = 8,  // baudrate counter width
  int unsigned DW = 8,  // shifter data width
  int unsigned SW = 1   // stop sequence width
)(
  // system signals
  input  logic          clk,
  input  logic          rst,
  // configuration
  input  logic [RW-1:0] cfg_bdr,  // baudrate
  input  logic [RW-1:0] cfg_smp,  // sample position
  // parallel stream (there is no READY signal)
  output logic          str_vld,  // valid
  output logic [DW-1:0] str_dat,  // data
  // serial RX output
  input  logic          rxd
);

// shift sequence length (start + data + stop)
localparam int unsigned SL = 1 + DW + SW;

// delay RDX and detect a start edge
logic          rxd_dly;
logic          rxd_edg;

// baudrate counter
logic [RW-1:0] bdr_cnt;
logic          bdr_end;
logic          bdr_smp;

// shifter bit counter
logic  [4-1:0] shf_cnt;
logic          shf_end;
logic          shf_run;

// shift data register
logic [DW+SW-1:0] shf_dat;

////////////////////////////////////////////////////////////////////////////////
// parallel stream
////////////////////////////////////////////////////////////////////////////////

// parallel stream valid
always_ff @(posedge clk, posedge rst)
if (rst)  str_vld <= 1'b0;
else      str_vld <= shf_end & bdr_smp;

////////////////////////////////////////////////////////////////////////////////
// start bit detection
////////////////////////////////////////////////////////////////////////////////

// delay uart_rxd and detect a start negative edge
always_ff @(posedge clk, posedge rst)
if (rst)  rxd_dly <= 1'b1;  // UART IDLE value
else      rxd_dly <= rxd;

// detect falling edge (transition from IDLE to START)
assign rxd_edg = rxd_dly & ~rxd;

////////////////////////////////////////////////////////////////////////////////
// serializer
////////////////////////////////////////////////////////////////////////////////

// baudrate generator from clock
always_ff @(posedge clk, posedge rst)
if (rst)        bdr_cnt <= '0;
else begin
  if (shf_run)  bdr_cnt <= bdr_end ? '0 : bdr_cnt + 1;
  else          bdr_cnt <= '0;
end

// enable signal for shifting and sample logic
assign bdr_end = bdr_cnt == cfg_bdr;
assign bdr_smp = bdr_cnt == cfg_smp;

// bit counter
always_ff @(posedge clk, posedge rst)
if (rst) begin
  shf_cnt <= 4'd0;
  shf_run <= 1'b0;
end else begin
  if (~shf_run) begin
    if (rxd_edg) begin
      shf_cnt <= 4'd0;
      shf_run <= 1'b1;
    end
  end else begin
    if (shf_end) begin
      if (bdr_smp) begin
        shf_cnt <= 4'd0;
        shf_run <= 1'b0;
      end
    end else begin
      if (bdr_end) begin
        shf_cnt <= shf_cnt + 1;
      end
    end
  end
end

// end of shift sequence
assign shf_end = shf_cnt == 4'(SL-1);

// data shift register
always_ff @(posedge clk)
if (shf_run) begin
  if (bdr_smp)  shf_dat <= {rxd, shf_dat[DW+SW-1:1]};
end

// parallel stream data (START is already shifted out when VALID is active)
assign str_dat = shf_dat[DW-1:0];

endmodule: tcb_uart_des
