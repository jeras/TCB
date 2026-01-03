////////////////////////////////////////////////////////////////////////////////
// TCB lite (Tightly Coupled Bus) SystemVerilog interface
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

interface tcb_lite_if #(
    // configuration parameters
    parameter int unsigned DELAY =  1,  // response delay
    parameter int unsigned WIDTH = 32,  // data/address width (only 32/64 are supported)
    parameter bit [WIDTH-1] MASK = '1,  // address mask
    parameter bit           MODE = '1   // bus mode (0-logarithmic size, 1-byte enable)
)(
    // system signals
    input  logic clk,  // clock
    input  logic rst   // reset
);

////////////////////////////////////////////////////////////////////////////////
// I/O ports
////////////////////////////////////////////////////////////////////////////////

    // handshake
    logic vld;  // valid
    logic rdy;  // ready

    // request
    logic               lck;  // arbitration lock
    logic               wen;  // write enable (0-read, 1-write)
    logic [WIDTH  -1:0] adr;  // address
    logic [      2-1:0] siz;  // transfer size
    logic [WIDTH/8-1:0] byt;  // byte enable
    logic [WIDTH  -1:0] wdt;  // write data

    // response
    logic [WIDTH  -1:0] rdt;  // read data
    logic               err;  // bus error

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// helper functions
////////////////////////////////////////////////////////////////////////////////

    // TODO: rethink this functionality
    // logarithmic size mode (subordinate interface) byte enable
    function automatic logic [WIDTH/8-1:0] siz2byt (
        input logic [2-1:0] siz
    );
        for (int unsigned i=0; i<WIDTH/8; i++) begin
            siz2byt[i] = (i < 2**siz) ? 1'b1 : 1'b0;
        end
    endfunction: siz2byt

////////////////////////////////////////////////////////////////////////////////
// transaction handshake
////////////////////////////////////////////////////////////////////////////////

    // handshake
    logic trn;  // transfer
    logic stl;  // stall
    logic idl;  // idle
    logic dly [0:DELAY];  // transfer delay

    // transfer (valid and ready at the same time)
    assign trn = vld & rdy;

    // stall (valid while not ready)
    assign stl = vld & ~rdy;

    // TODO: improve description
    // idle (either not valid or ending the current cycle with a transfer)
    assign idl = ~vld | trn;

    // delay line
    assign dly[0] = trn;
    generate
    if (DELAY > 0) begin: delay
        always_ff @(posedge clk)
        dly[1:DELAY] <= dly[0:DELAY-1];
    end: delay
    endgenerate

////////////////////////////////////////////////////////////////////////////////
// modports
////////////////////////////////////////////////////////////////////////////////

    // manager
    modport  man (
        // system signals
        input  clk,
        input  rst,
        // handshake
        output vld,
        input  rdy,
        // local signals
        input  trn,
        input  stl,
        input  idl,
        input  dly,
        // request
        output lck,
        output wen,
        output adr,
        output siz,
        output byt,
        output wdt,
        // response
        input  rdt,
        input  err
    );

    // monitor
    modport  mon (
        // system signals
        input  clk,
        input  rst,
        // handshake
        input  vld,
        input  rdy,
        // local signals
        input  trn,
        input  stl,
        input  idl,
        input  dly,
        // request
        input  lck,
        input  wen,
        input  adr,
        input  siz,
        input  byt,
        input  wdt,
        // response
        input  rdt,
        input  err
    );

    // subordinate
    modport  sub (
        // system signals
        input  clk,
        input  rst,
        // handshake
        input  vld,
        output rdy,
        // local signals
        input  trn,
        input  stl,
        input  idl,
        input  dly,
        // request
        input  lck,
        input  wen,
        input  adr,
        input  siz,
        input  byt,
        input  wdt,
        // response
        output rdt,
        output err
    );

endinterface: tcb_lite_if
