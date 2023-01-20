////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library endianness converter
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

module tcb_lib_endianness #(
)(
  tcb_if.sub sub,  // TCB subordinate port (manager     device connects here)
  tcb_if.man man,  // TCB manager     port (subordinate device connects here)
  // outputs
  output logic mal   // missalligned access
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
  // camparing subordinate and manager interface parameters
  generate
    // bus widths
    if (sub.ABW != man.ABW)  $error("ERROR: %m parameter (sub.ABW = %d) != (man.ABW = %d)", sub.ABW, man.ABW);
    if (sub.DBW != man.DBW)  $error("ERROR: %m parameter (sub.DBW = %d) != (man.DBW = %d)", sub.DBW, man.DBW);
    if (sub.SLW != man.SLW)  $error("ERROR: %m parameter (sub.SLW = %d) != (man.SLW = %d)", sub.SLW, man.SLW);
    if (sub.BEW != man.BEW)  $error("ERROR: %m parameter (sub.BEW = %d) != (man.BEW = %d)", sub.BEW, man.BEW);
    // response delay
    if (sub.DLY != man.DLY)  $error("ERROR: %m parameter (sub.DLY = %d) != (man.DLY = %d)", sub.DLY, man.DLY);
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// misalignment
////////////////////////////////////////////////////////////////////////////////

  // decodings for read and write access are identical
  always_comb
  unique case (sub.siz)
    'd0    : mal = 1'b0;
    'd1    : mal = |sub.adr[0:0];
    'd2    : mal = |sub.adr[1:0];
    'd3    : mal = |sub.adr[2:0];
    default: mal = 1'bx;
  endcase

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

  // write data packed arrays
  logic [sub.BEW-1:0][sub.SLW-1:0] sub_wdt;
  logic [man.BEW-1:0][man.SLW-1:0] man_wdt;

  // write data multiplexer select
  logic [$clog2(sub.BEW)-1:0] mux_wdt [man.BEW-1:0];

  // write data packed array from vector
  assign sub_wdt = sub.wdt;

  // write data bytes
  generate
  for (genvar i=0; i<man.BEW; i++) begin
  
    // select signal
    assign mux_wdt[i] = ~man.adr[$clog2(sub.BEW)-1:0];

    // byte enable
    assign man.ben[i] = '1;

    // multiplexer
    assign man_wdt[i] = sub_wdt[mux_wdt[i]];
  
  end
  endgenerate

  // write data packed array to vector 
  assign man.wdt = man_wdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // read data packed arrays
  logic [man.BEW-1:0][man.SLW-1:0] man_rdt;
  logic [sub.BEW-1:0][sub.SLW-1:0] sub_rdt;

  // read data multiplexer select
  logic [$clog2(sub.BEW)-1:0] mux_rdt [man.BEW-1:0];

  // read data packed array from vector
  assign man.rdt = man_rdt;

  // write data bytes
  generate
  for (genvar i=0; i<man.BEW; i++) begin
  
    // select signal
    assign mux_rdt[i] = ~man.adr[$clog2(sub.BEW)-1:0];

    // multiplexer
    assign sub_rdt[i] = man_rdt[mux_rdt[i]];
  
  end
  endgenerate

  // read data packed array to vector 
  assign sub_rdt = sub.rdt;

/*
// read alignment delayed signals
logic            dly_rma;
logic   [WW-1:0] dly_adr;
fn3_ldu_et       dly_fn3;

logic [XLEN-1:0] dly_dat;  // data
logic   [32-1:0] dly_dtw;  // data word
logic   [16-1:0] dly_dth;  // data half
logic   [ 8-1:0] dly_dtb;  // data byte


// read alignment
always_ff @ (posedge clk, posedge rst)
if (rst) begin
  dly_rma <= 1'b0;
  dly_adr <= '0;
  dly_fn3 <= XLEN == 32 ? LW : LD;
end else if (lsb_rtr) begin
  dly_rma <= rma;
  dly_adr <= adr[WW-1:0];
  dly_fn3 <= ctl.ldu.fn3;
end

// read data
always_comb begin: blk_rdt
  // read data multiplexer
  dly_dtw = lsb_rdt[31: 0];
  dly_dth = dly_adr[1] ? dly_dtw[31:16] : dly_dtw[15: 0];
  dly_dtb = dly_adr[0] ? dly_dth[15: 8] : dly_dth[ 7: 0];
  // read data multiplexer
  dly_dat = {dly_dtw[31:16], dly_dth[15: 8], dly_dtb[ 7: 0]};
  // sign extension
  // NOTE: this is a good fit for LUT4
  unique case (dly_fn3)
    LB     : rdt = DW'(  $signed( 8'(dly_dat)));
    LH     : rdt = DW'(  $signed(16'(dly_dat)));
    LW     : rdt = DW'(  $signed(32'(dly_dat)));
    LBU    : rdt = DW'($unsigned( 8'(dly_dat)));
    LHU    : rdt = DW'($unsigned(16'(dly_dat)));
    LWU    : rdt = DW'($unsigned(32'(dly_dat)));  // Quartus does a better job if this line is present
    default: rdt = 'x;
  endcase
end: blk_rdt

// system stall
assign rdy = lsb_rdy;
*/
endmodule: tcb_lib_endianness
