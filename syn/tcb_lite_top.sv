////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) synthesis test top
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

module tcb_lite_top #(
    // RTL configuration parameters
    parameter  int unsigned  DLY =    1,  // response delay
    parameter  int unsigned  DAT =   32,  // data    width (only 32/64 are supported)
    parameter  int unsigned  ADR =  DAT,  // address width (only 32/64 are supported)
    parameter  bit [ADR-1:0] MSK =   '1,  // address mask
    parameter  bit           MOD = 1'b1,  // bus mode (0-logarithmic size, 1-byte enable)
    // local parameters
    localparam int unsigned  BYT = DAT/8,        // byte enable width
    localparam int unsigned  MAX = $clog2(BYT),  // maximum logarithmic size
    localparam int unsigned  SIZ = $clog2(BYT)   // logarithmic size width
)(
    // system signals
    input  logic clk = 1'b1,  // clock
    input  logic rst = 1'b1,  // reset
    // subordinate IF
    input  logic           sub_vld    ,  // handshake: valid
    output logic           sub_rdy    ,  // handshake: ready
    input  logic           sub_req_lck,  // request: arbitration lock
    input  logic           sub_req_ndn,  // request: endianness (0-little, 1-big)
    input  logic           sub_req_wen,  // request: write enable (0-read, 1-write)
    input  logic [ADR-1:0] sub_req_adr,  // request: address
    input  logic [SIZ-1:0] sub_req_siz,  // request: transfer size
    input  logic [BYT-1:0] sub_req_byt,  // request: byte enable
    input  logic [DAT-1:0] sub_req_wdt,  // request: write data
    output logic [DAT-1:0] sub_rsp_rdt,  // response: read data
    output logic           sub_rsp_err,  // response: bus error
    // manager IF
    output logic           man_vld    ,  // handshake: valid
    input  logic           man_rdy    ,  // handshake: ready
    output logic           man_req_lck,  // request: arbitration lock
    output logic           man_req_ndn,  // request: endianness (0-little, 1-big)
    output logic           man_req_wen,  // request: write enable (0-read, 1-write)
    output logic [ADR-1:0] man_req_adr,  // request: address
    output logic [SIZ-1:0] man_req_siz,  // request: transfer size
    output logic [BYT-1:0] man_req_byt,  // request: byte enable
    output logic [DAT-1:0] man_req_wdt,  // request: write data
    input  logic [DAT-1:0] man_rsp_rdt,  // response: read data
    input  logic           man_rsp_err   // response: bus error
);

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // TCB interfaces
    tcb_lite_if #(DLY, DAT, ADR, MSK, MOD) tcb_sub (.clk (clk), .rst (rst));
    tcb_lite_if #(DLY, DAT, ADR, MSK, MOD) tcb_man (.clk (clk), .rst (rst));

////////////////////////////////////////////////////////////////////////////////
// DUT instances
////////////////////////////////////////////////////////////////////////////////

    // subordinate ports
    assign tcb_sub.vld     =         sub_vld    ;
    assign     sub_rdy     =     tcb_sub.rdy    ;
    assign tcb_sub.req.lck =         sub_req_lck;
    assign tcb_sub.req.ndn =         sub_req_ndn;
    assign tcb_sub.req.wen =         sub_req_wen;
    assign tcb_sub.req.adr =         sub_req_adr;
    assign tcb_sub.req.siz =         sub_req_siz;
    assign tcb_sub.req.byt =         sub_req_byt;
    assign tcb_sub.req.wdt =         sub_req_wdt;
    assign     sub_rsp_rdt     = tcb_sub.rsp.rdt;
    assign     sub_rsp_err     = tcb_sub.rsp.err;

    // passthrough
    tcb_lite_lib_passthrough dut (
        .sub (tcb_sub),
        .man (tcb_man)
    );

    // manager ports
    assign     sub_vld     = tcb_sub.vld    ;
    assign tcb_sub.rdy     =     sub_rdy    ;
    assign     sub_req_lck = tcb_sub.req.lck;
    assign     sub_req_ndn = tcb_sub.req.ndn;
    assign     sub_req_wen = tcb_sub.req.wen;
    assign     sub_req_adr = tcb_sub.req.adr;
    assign     sub_req_siz = tcb_sub.req.siz;
    assign     sub_req_byt = tcb_sub.req.byt;
    assign     sub_req_wdt = tcb_sub.req.wdt;
    assign tcb_sub.rsp.rdt =     sub_rsp_rdt;
    assign tcb_sub.rsp.err =     sub_rsp_err;

endmodule: tcb_lite_top
