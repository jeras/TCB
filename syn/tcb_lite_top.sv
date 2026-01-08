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
    input  logic           sub_vld,  // handshake: valid
    output logic           sub_rdy,  // handshake: ready
    input  logic           sub_lck,  // request: arbitration lock
    input  logic           sub_ndn,  // request: endianness (0-little, 1-big)
    input  logic           sub_wen,  // request: write enable (0-read, 1-write)
    input  logic [ADR-1:0] sub_adr,  // request: address
    input  logic [SIZ-1:0] sub_siz,  // request: transfer size
    input  logic [BYT-1:0] sub_byt,  // request: byte enable
    input  logic [DAT-1:0] sub_wdt,  // request: write data
    output logic [DAT-1:0] sub_rdt,  // response: read data
    output logic           sub_err,  // response: bus error
    // manager IF
    output logic           man_vld,  // handshake: valid
    input  logic           man_rdy,  // handshake: ready
    output logic           man_lck,  // request: arbitration lock
    output logic           man_ndn,  // request: endianness (0-little, 1-big)
    output logic           man_wen,  // request: write enable (0-read, 1-write)
    output logic [ADR-1:0] man_adr,  // request: address
    output logic [SIZ-1:0] man_siz,  // request: transfer size
    output logic [BYT-1:0] man_byt,  // request: byte enable
    output logic [DAT-1:0] man_wdt,  // request: write data
    input  logic [DAT-1:0] man_rdt,  // response: read data
    input  logic           man_err   // response: bus error
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
    assign tcb_sub.vld =     sub_vld;
    assign     sub_rdy = tcb_sub.rdy;
    assign tcb_sub.lck =     sub_lck;
    assign tcb_sub.ndn =     sub_ndn;
    assign tcb_sub.wen =     sub_wen;
    assign tcb_sub.adr =     sub_adr;
    assign tcb_sub.siz =     sub_siz;
    assign tcb_sub.byt =     sub_byt;
    assign tcb_sub.wdt =     sub_wdt;
    assign     sub_rdt = tcb_sub.rdt;
    assign     sub_err = tcb_sub.err;

    // passthrough
    tcb_lite_lib_passthrough dut (
        .sub (tcb_sub),
        .man (tcb_man)
    );

    // manager ports
    assign     sub_vld = tcb_sub.vld;
    assign tcb_sub.rdy =     sub_rdy;
    assign     sub_lck = tcb_sub.lck;
    assign     sub_ndn = tcb_sub.ndn;
    assign     sub_wen = tcb_sub.wen;
    assign     sub_adr = tcb_sub.adr;
    assign     sub_siz = tcb_sub.siz;
    assign     sub_byt = tcb_sub.byt;
    assign     sub_wdt = tcb_sub.wdt;
    assign tcb_sub.rdt =     sub_rdt;
    assign tcb_sub.err =     sub_err;

endmodule: tcb_lite_top
