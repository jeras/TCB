////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) SystemVerilog interface
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

interface tcb_lite_if
    import tcb_lite_pkg::*;
#(
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
    localparam int unsigned BYT = DAT/8;          // byte enable width
    localparam int unsigned MAX = $clog2(BYT);    // maximum logarithmic size
    localparam int unsigned SIZ = $clog2(MAX+1);  // logarithmic size width

    // request type
    typedef struct {
        logic           lck;  // arbitration lock
        logic           ndn;  // endianness (0-little, 1-big)
        logic           wen;  // write enable (0-read, 1-write)
        logic [ADR-1:0] adr;  // address
        logic [SIZ-1:0] siz;  // transfer size
        logic [BYT-1:0] byt;  // byte enable
        logic [DAT-1:0] wdt;  // write data
    } req_t;

    // response type
    typedef struct {
        logic [DAT-1:0] rdt;  // read data
        logic           err;  // bus error
    } rsp_t;

////////////////////////////////////////////////////////////////////////////////
// I/O ports
////////////////////////////////////////////////////////////////////////////////

    // handshake
    logic vld;  // valid
    logic rdy;  // ready

    // request/response
    req_t req;
    rsp_t rsp;

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

    // delay line
    logic trn_dly [0:DLY];  // handshake transfer
    req_t req_dly [0:DLY];  // request
    rsp_t rsp_dly [0:DLY];  // response

    // zero delay (continuous assignment)
    assign trn_dly[0] = trn;
    assign req_dly[0] = req;

    generate
        // handshake/request delay line
        for (genvar i=1; i<=DLY; i++) begin: dly
            logic trn_tmp;
            req_t req_tmp;
            // continuous assignment
            assign trn_dly[i] = trn_tmp;
            assign req_dly[i] = req_tmp;
            // propagate through delay line
            always_ff @(posedge clk)
            begin
                trn_tmp <= trn_dly[i-1];
                if (trn_dly[i-1]) begin
                    req_tmp <= req_dly[i-i];
                end
            end
        end: dly

        if (VIP) begin: vip
            // response delay line
            for (genvar i=1; i<=DLY; i++) begin: dly
                rsp_t rsp_tmp;
                // continuous assignment
                assign rsp_dly[i] = rsp_tmp;
                // propagate through delay line
                always_ff @(posedge clk)
                begin
                    if (trn_dly[i-1]) begin
                        rsp_tmp <= rsp_dly[i-i];
                    end
                end
            end: dly
            // continuous assignment
            if (DLY == 0) begin
                assign rsp = trn ? rsp_dly[DLY] : '{default: 'z};
            end else begin
                if (HLD)  assign rsp =                rsp_dly[DLY];
                else      assign rsp = trn_dly[DLY] ? rsp_dly[DLY] : '{default: 'x};
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
        // request/response
        output req,
        input  rsp,
        // delay line
        input  trn_dly,
        input  req_dly,
        input  rsp_dly
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
        // request/response
        input  req,
        input  rsp,
        // delay line
        input  trn_dly,
        input  req_dly,
        input  rsp_dly
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
        // request/response
        input  req,
        output rsp,
        // delay line
        input  trn_dly,
        input  req_dly,
        input  rsp_dly
    );

endinterface: tcb_lite_if
