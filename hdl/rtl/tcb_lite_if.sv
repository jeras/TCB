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
    // configuration parameters
    parameter tcb_lite_cfg_t CFG = TCB_LITE_CFG_DEF
)(
    // system signals
    input  logic clk,  // clock
    input  logic rst   // reset
);

    // local parameters (calculated from configuration)
    localparam int unsigned CFG_BUS_BYT = CFG.BUS.DAT/8;          // byte enable width
    localparam int unsigned CFG_BUS_OFF = $clog2(CFG_BUS_BYT);    // address offset size
    localparam int unsigned CFG_BUS_SIZ = $clog2(CFG_BUS_OFF+1);  // logarithmic size width

    // request type
    typedef struct {
        logic                   lck;  // arbitration lock
        logic                   wen;  // write enable
        logic                   ren;  // read  enable
        logic                   ndn;  // endianness (0-little, 1-big)
        logic [CFG.BUS.CTL-1:0] ctl;  // control (user defined request signals)
        logic [CFG.BUS.ADR-1:0] adr;  // address
        logic [CFG_BUS_SIZ-1:0] siz;  // transfer size
        logic [CFG_BUS_BYT-1:0] byt;  // byte enable
        logic [CFG.BUS.DAT-1:0] wdt;  // write data
    } req_t;

    // response type
    typedef struct {
        logic [CFG.BUS.DAT-1:0] rdt;  // read data
        logic [CFG.BUS.STS-1:0] sts;  // response status (user defined response signals)
        logic                   err;  // response error
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
    logic trn_dly [0:CFG.HSK.DLY];  // handshake transfer
    req_t req_dly [0:CFG.HSK.DLY];  // request

    // zero delay (continuous assignment)
    assign trn_dly[0] = trn;
    assign req_dly[0] = req;

    // handshake/request delay line
    generate
    for (genvar i=1; i<=CFG.HSK.DLY; i++) begin: dly
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
        input  req_dly
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
        input  req_dly
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
        input  req_dly
    );

endinterface: tcb_lite_if
