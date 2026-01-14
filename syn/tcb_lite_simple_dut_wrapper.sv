////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) DUT (synthesis test top wrapper)
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

module tcb_lite_dut_wrapper #(
    // RTL configuration parameters
    parameter  int unsigned  DLY =    1,  // response delay
    parameter  int unsigned  DAT =   32,  // data    width (only 32/64 are supported)
    parameter  int unsigned  ADR =  DAT,  // address width (only 32/64 are supported)
    parameter  bit [ADR-1:0] MSK =   '1,  // address mask
    parameter  bit           MOD = 1'b1,  // bus mode (0-logarithmic size, 1-byte enable)
    // local parameters
    localparam int unsigned  BYT = DAT/8,          // byte enable width
    localparam int unsigned  MAX = $clog2(BYT),    // maximum logarithmic size
    localparam int unsigned  SIZ = $clog2(MAX+1),  // logarithmic size width
    // select the DUT to test
    parameter  string        DUT = "PASSTHROUGH"
)(
    // system signals
    input  logic clk,  // clock
    input  logic rst,  // reset
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

    // subordinate interface
    assign tcb_sub.vld     = sub_vld    ;
    assign tcb_sub.req.lck = sub_req_lck;
    assign tcb_sub.req.ndn = sub_req_ndn;
    assign tcb_sub.req.wen = sub_req_wen;
    assign tcb_sub.req.adr = sub_req_adr;
    assign tcb_sub.req.siz = sub_req_siz;
    assign tcb_sub.req.byt = sub_req_byt;
    assign tcb_sub.req.wdt = sub_req_wdt;
    assign sub_rsp_rdt = tcb_sub.rsp.rdt;
    assign sub_rsp_err = tcb_sub.rsp.err;
    assign sub_rdy     = tcb_sub.rdy    ;

    // DUT instances
    generate
    case (DUT)
        "PASSTHROUGH": begin: passthrough
            tcb_lite_lib_passthrough dut (
                .sub  (tcb_sub),
                .man  (tcb_man)
            );
        end: passthrough
        "REGISTER_BACKPRESSURE": begin: register_backpressure
            tcb_lite_lib_register_backpressure dut (
                .sub  (tcb_sub),
                .man  (tcb_man)
            );
        end: register_backpressure
        "REGISTER_REQUEST": begin: register_request
            tcb_lite_lib_register_request dut (
                .sub  (tcb_sub),
                .man  (tcb_man)
            );
        end: register_request
        "REGISTER_RESPONSE": begin: register_response
            tcb_lite_lib_register_response dut (
                .sub  (tcb_sub),
                .man  (tcb_man)
            );
        end: register_response
        "LOGSIZE2BYTEENA": begin: logsize2byteena
            tcb_lite_lib_logsize2byteena dut (
                .sub  (tcb_sub),
                .man  (tcb_man)
            );
        end: logsize2byteena
//        "READ_MODIFY_WRITE": begin: read_modify_write
//            tcb_lib_read_modify_write dut (
//                .sub  (tcb_sub),
//                .man  (tcb_man)
//            );
//        end: read_modify_write
        default: begin: undefined
            initial $error("DUT module not recognized.");
        end: undefined
    endcase
    endgenerate
    
    // manager interface
    assign man_vld     = tcb_man.vld    ;
    assign man_req_lck = tcb_man.req.lck;
    assign man_req_ndn = tcb_man.req.ndn;
    assign man_req_wen = tcb_man.req.wen;
    assign man_req_adr = tcb_man.req.adr;
    assign man_req_siz = tcb_man.req.siz;
    assign man_req_byt = tcb_man.req.byt;
    assign man_req_wdt = tcb_man.req.wdt;
    assign tcb_man.rsp.rdt = man_rsp_rdt;
    assign tcb_man.rsp.err = man_rsp_err;
    assign tcb_man.rdy     = man_rdy    ;

endmodule: tcb_lite_dut_wrapper
