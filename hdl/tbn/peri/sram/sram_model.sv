////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) SystemVerilog interface
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

module sram_model #(
  parameter  int unsigned DAT = 8,  // data bus width
  parameter  int unsigned ADR = 8,  // address bus width
  parameter  int unsigned SIZ = 2**ADR  // memory size
)(
  input  logic           clk,  // clock
  input  logic           cen,  // chip enable
  input  logic           wen,  // write enable
  input  logic [ADR-1:0] adr,  // address
  input  logic [DAT-1:0] wdt,  // write data
  output logic [DAT-1:0] rdt   // read data
);

  logic [DAT-1:0] mem [0:SIZ-1];

  // read first SRAM
  always_ff @(posedge clk)
  if (cen) begin
    if (wen) begin
      mem[adr] <= wdt;
    end else begin
      rdt <= mem[adr];
    end
  end

endmodule: sram_model
