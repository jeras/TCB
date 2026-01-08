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
    // RTL configuration parameters
    parameter  int unsigned  DLY =    1,  // response delay
    parameter  int unsigned  DAT =   32,  // data    width (only 32/64 are supported)
    parameter  int unsigned  ADR =  DAT,  // address width (only 32/64 are supported)
    parameter  bit [ADR-1:0] MSK =   '1,  // address mask
    parameter  bit           MOD = 1'b1,  // bus mode (0-logarithmic size, 1-byte enable)
    // VIP configuration parameters
    parameter  bit           VIP = 1'b0,  // enable VIP functionality
    parameter  bit           HLD = 1'b0   // hold last response stable
)(
    // system signals
    input  logic clk,  // clock
    input  logic rst   // reset
);

    // local parameters
    localparam int unsigned BYT = DAT/8;        // byte enable width
    localparam int unsigned MAX = $clog2(BYT);  // maximum logarithmic size
    localparam int unsigned SIZ = $clog2(BYT);  // logarithmic size width

////////////////////////////////////////////////////////////////////////////////
// I/O ports
////////////////////////////////////////////////////////////////////////////////

    // handshake
    logic vld;  // valid
    logic rdy;  // ready

    // request
    logic           lck;  // arbitration lock
    logic           ndn;  // endianness (0-little, 1-big)
    logic           wen;  // write enable (0-read, 1-write)
    logic [ADR-1:0] adr;  // address
    logic [SIZ-1:0] siz;  // transfer size
    logic [BYT-1:0] byt;  // byte enable
    logic [DAT-1:0] wdt;  // write data

    // response
    logic [DAT-1:0] rdt;  // read data
    logic           err;  // bus error

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// helper functions
////////////////////////////////////////////////////////////////////////////////

    // TODO: rethink this functionality
    // logarithmic size mode (subordinate interface) byte enable
    function automatic logic [BYT-1:0] siz2byt (
        input logic [2-1:0] siz
    );
        for (int unsigned i=0; i<BYT; i++) begin
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

    // transfer (valid and ready at the same time)
    assign trn = vld & rdy;

    // stall (valid while not ready)
    assign stl = vld & ~rdy;

    // TODO: improve description
    // idle (either not valid or ending the current cycle with a transfer)
    assign idl = ~vld | trn;

////////////////////////////////////////////////////////////////////////////////
// request/response delay
////////////////////////////////////////////////////////////////////////////////

    // transfer
    logic           trn_dly [0:DLY];  // transfer

    // request
    logic           lck_dly [0:DLY];  // arbitration lock
    logic           ndn_dly [0:DLY];  // endianness (0-little, 1-big)
    logic           wen_dly [0:DLY];  // write enable (0-read, 1-write)
    logic [DAT-1:0] adr_dly [0:DLY];  // address
    logic [SIZ-1:0] siz_dly [0:DLY];  // transfer size
    logic [BYT-1:0] byt_dly [0:DLY];  // byte enable
    logic [DAT-1:0] wdt_dly [0:DLY];  // write data

    // response
    logic [DAT-1:0] rdt_dly [0:DLY];  // read data
    logic           err_dly [0:DLY];  // bus error

    // transfer delay (continuous assignment)
    assign trn_dly[0] = trn;
    // request delay (continuous assignment)
    assign lck_dly[0] = lck;
    assign ndn_dly[0] = ndn;
    assign wen_dly[0] = wen;
    assign adr_dly[0] = adr;
    assign siz_dly[0] = siz;
    assign byt_dly[0] = byt;
    assign wdt_dly[0] = wdt;

    generate
        // delay line
        for (genvar i=1; i<=DLY; i++) begin: dly
            // transfer
            logic           trn_tmp;  // transfer
            // request
            logic           lck_tmp;  // arbitration lock
            logic           ndn_tmp;  // endianness (0-little, 1-big)
            logic           wen_tmp;  // write enable (0-read, 1-write)
            logic [DAT-1:0] adr_tmp;  // address
            logic [SIZ-1:0] siz_tmp;  // transfer size
            logic [BYT-1:0] byt_tmp;  // byte enable
            logic [DAT-1:0] wdt_tmp;  // write data
            
            // transfer (continuous assignment)
            assign trn_dly[i] = trn_tmp;
            // request (continuous assignment)
            assign lck_dly[i] = lck_tmp;
            assign ndn_dly[i] = ndn_tmp;
            assign wen_dly[i] = wen_tmp;
            assign adr_dly[i] = adr_tmp;
            assign siz_dly[i] = siz_tmp;
            assign byt_dly[i] = byt_tmp;
            assign wdt_dly[i] = wdt_tmp;

            // propagate through delay line
            always_ff @(posedge clk)
            begin
                trn_tmp <= trn_dly[i-1];
                if (trn_dly[i-1]) begin
                    lck_tmp <= lck_dly[i-i];
                    ndn_tmp <= ndn_dly[i-i];
                    wen_tmp <= wen_dly[i-i];
                    adr_tmp <= adr_dly[i-i];
                    siz_tmp <= siz_dly[i-i];
                    byt_tmp <= byt_dly[i-i];
                    wdt_tmp <= wdt_dly[i-i];
                end
            end
        end: dly

        if (VIP) begin: vip
            // continuous assignment
            if (DLY == 0) begin
                assign rdt = trn ? rdt_dly[DLY] : 'z;
                assign err = trn ? err_dly[DLY] : 'z;
            end else begin
                if (HLD) begin
                    assign rdt =                rdt_dly[DLY];
                    assign err =                err_dly[DLY];
                end else begin
                    assign rdt = trn_dly[DLY] ? rdt_dly[DLY] : 'x;
                    assign err = trn_dly[DLY] ? err_dly[DLY] : 'x;
                end
            end
        end: vip

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
        // request
        output lck,
        output ndn,
        output wen,
        output adr,
        output siz,
        output byt,
        output wdt,
        // response
        input  rdt,
        input  err,
        // transfer (delay line)
        input  trn_dly,
        // request (delay line)
        input  lck_dly,
        input  ndn_dly,
        input  wen_dly,
        input  adr_dly,
        input  siz_dly,
        input  byt_dly,
        input  wdt_dly,
        // response (delay line)
        input  rdt_dly,
        input  err_dly
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
        // request
        input  lck,
        input  ndn,
        input  wen,
        input  adr,
        input  siz,
        input  byt,
        input  wdt,
        // response
        input  rdt,
        input  err,
        // transfer (delay line)
        input  trn_dly,
        // request (delay line)
        input  lck_dly,
        input  ndn_dly,
        input  wen_dly,
        input  adr_dly,
        input  siz_dly,
        input  byt_dly,
        input  wdt_dly,
        // response (delay line)
        input  rdt_dly,
        input  err_dly
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
        // request
        input  lck,
        input  ndn,
        input  wen,
        input  adr,
        input  siz,
        input  byt,
        input  wdt,
        // response
        output rdt,
        output err,
        // transfer (delay line)
        input  trn_dly,
        // request (delay line)
        input  lck_dly,
        input  ndn_dly,
        input  wen_dly,
        input  adr_dly,
        input  siz_dly,
        input  byt_dly,
        input  wdt_dly,
        // response (delay line)
        input  rdt_dly,
        input  err_dly
    );

endinterface: tcb_lite_if
