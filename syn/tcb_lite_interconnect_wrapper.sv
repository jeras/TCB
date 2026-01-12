////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) interconnect (synthesis test top wrapper)
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

module tcb_lite_interconnect_wrapper #(
    // RTL configuration parameters
    parameter  int unsigned  DLY =    1,  // response delay
    parameter  int unsigned  DAT =   32,  // data    width (only 32/64 are supported)
    parameter  int unsigned  ADR =  DAT,  // address width (only 32/64 are supported)
    parameter  bit [ADR-1:0] MSK =   '1,  // address mask
    parameter  bit           MOD = 1'b1,  // bus mode (0-logarithmic size, 1-byte enable)
    // local parameters
    localparam int unsigned  BYT = DAT/8,        // byte enable width
    localparam int unsigned  MAX = $clog2(BYT),  // maximum logarithmic size
    localparam int unsigned  SIZ = $clog2(BYT),  // logarithmic size width
    // interface array parameters
    parameter  int unsigned  DUT_INN = 2,        // DUT instance number
    parameter  int unsigned  SUB_IFN = DUT_INN,  // subordinate interface number
    parameter  int unsigned  MAN_IFN = DUT_INN   // manager     interface number
)(
    // system signals
    input  logic clk,  // clock
    input  logic rst,  // reset
    // subordinate IF
    input  logic           sub_vld    [SUB_IFN-1:0],  // handshake: valid
    output logic           sub_rdy    [SUB_IFN-1:0],  // handshake: ready
    input  logic           sub_req_lck[SUB_IFN-1:0],  // request: arbitration lock
    input  logic           sub_req_ndn[SUB_IFN-1:0],  // request: endianness (0-little, 1-big)
    input  logic           sub_req_wen[SUB_IFN-1:0],  // request: write enable (0-read, 1-write)
    input  logic [ADR-1:0] sub_req_adr[SUB_IFN-1:0],  // request: address
    input  logic [SIZ-1:0] sub_req_siz[SUB_IFN-1:0],  // request: transfer size
    input  logic [BYT-1:0] sub_req_byt[SUB_IFN-1:0],  // request: byte enable
    input  logic [DAT-1:0] sub_req_wdt[SUB_IFN-1:0],  // request: write data
    output logic [DAT-1:0] sub_rsp_rdt[SUB_IFN-1:0],  // response: read data
    output logic           sub_rsp_err[SUB_IFN-1:0],  // response: bus error
    // manager IF
    output logic           man_vld    [MAN_IFN-1:0],  // handshake: valid
    input  logic           man_rdy    [MAN_IFN-1:0],  // handshake: ready
    output logic           man_req_lck[MAN_IFN-1:0],  // request: arbitration lock
    output logic           man_req_ndn[MAN_IFN-1:0],  // request: endianness (0-little, 1-big)
    output logic           man_req_wen[MAN_IFN-1:0],  // request: write enable (0-read, 1-write)
    output logic [ADR-1:0] man_req_adr[MAN_IFN-1:0],  // request: address
    output logic [SIZ-1:0] man_req_siz[MAN_IFN-1:0],  // request: transfer size
    output logic [BYT-1:0] man_req_byt[MAN_IFN-1:0],  // request: byte enable
    output logic [DAT-1:0] man_req_wdt[MAN_IFN-1:0],  // request: write data
    input  logic [DAT-1:0] man_rsp_rdt[MAN_IFN-1:0],  // response: read data
    input  logic           man_rsp_err[MAN_IFN-1:0]   // response: bus error
);

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // TCB interfaces
    tcb_lite_if #(DLY, DAT, ADR, MSK, MOD) tcb_sub [SUB_IFN-1:0] (.clk (clk), .rst (rst));
    tcb_lite_if #(DLY, DAT, ADR, MSK, MOD) tcb_man [MAN_IFN-1:0] (.clk (clk), .rst (rst));

////////////////////////////////////////////////////////////////////////////////
// DUT instances
////////////////////////////////////////////////////////////////////////////////

    // subordinate interfaces
    generate
    for (genvar i=0; i<SUB_IFN; i++) begin: sub_ifn
        assign tcb_sub[i].vld     = sub_vld    [i];
        assign tcb_sub[i].req.lck = sub_req_lck[i];
        assign tcb_sub[i].req.ndn = sub_req_ndn[i];
        assign tcb_sub[i].req.wen = sub_req_wen[i];
        assign tcb_sub[i].req.adr = sub_req_adr[i];
        assign tcb_sub[i].req.siz = sub_req_siz[i];
        assign tcb_sub[i].req.byt = sub_req_byt[i];
        assign tcb_sub[i].req.wdt = sub_req_wdt[i];
        assign sub_rsp_rdt[i] = tcb_sub[i].rsp.rdt;
        assign sub_rsp_err[i] = tcb_sub[i].rsp.err;
        assign sub_rdy    [i] = tcb_sub[i].rdy    ;
    end: sub_ifn
    endgenerate

    // dut instances
    generate
    for (genvar i=0; i<SUB_IFN; i++) begin: dut_ifn
        tcb_lite_lib_passthrough dut (
            .sub (tcb_sub[i]),
            .man (tcb_man[i])
        );
    end: dut_ifn
    endgenerate

    // manager interfaces
    generate
    for (genvar i=0; i<MAN_IFN; i++) begin: man_ifn
        assign man_vld    [i] = tcb_man[i].vld    ;
        assign man_req_lck[i] = tcb_man[i].req.lck;
        assign man_req_ndn[i] = tcb_man[i].req.ndn;
        assign man_req_wen[i] = tcb_man[i].req.wen;
        assign man_req_adr[i] = tcb_man[i].req.adr;
        assign man_req_siz[i] = tcb_man[i].req.siz;
        assign man_req_byt[i] = tcb_man[i].req.byt;
        assign man_req_wdt[i] = tcb_man[i].req.wdt;
        assign tcb_man[i].rsp.rdt = man_rsp_rdt[i];
        assign tcb_man[i].rsp.err = man_rsp_err[i];
        assign tcb_man[i].rdy     = man_rdy    [i];
    end: man_ifn
    endgenerate

endmodule: tcb_lite_interconnect_wrapper
