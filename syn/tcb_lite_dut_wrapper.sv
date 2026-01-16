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
    parameter  bit           HLD = 1'b0,  // response delay
    parameter  bit           MOD = 1'b1,  // bus mode (0-logarithmic size, 1-byte enable)
    parameter  int unsigned  CTL =    0,  // control width (user defined request signals)
    parameter  int unsigned  ADR =   32,  // address width (only 32/64 are supported)
    parameter  int unsigned  DAT =   32,  // data    width (only 32/64 are supported)
    parameter  int unsigned  STS =    0,  // status  width (user defined response signals)
//  parameter  bit [ADR-1:0] MSK =   '1,  // address mask
    // local parameters
    localparam int unsigned  BYT = DAT/8,        // byte enable width
    localparam int unsigned  MAX = $clog2(BYT),  // maximum logarithmic size
    localparam int unsigned  SIZ = $clog2(BYT),  // logarithmic size width
    // interface array parameters
    parameter  int unsigned  DUT_INN = 1,        // DUT instance number
    parameter  int unsigned  SUB_IFN = DUT_INN,  // subordinate interface number
    parameter  int unsigned  MAN_IFN = DUT_INN,  // manager     interface number
    // select the DUT to test
    parameter  string        DUT = "PASSTHROUGH"
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

    import tcb_lite_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

    // logarithms of interface numbers
    localparam int unsigned SUB_IFL = $clog2(SUB_IFN);  // subordinate interface number
    localparam int unsigned MAN_IFL = $clog2(MAN_IFN);  // manager     interface number

    // response delay
    localparam int unsigned SUB_DLY = ((DUT == "REGISTER_REQUEST") || (DUT == "REGISTER_RESPONSE")) ? DLY+1 : DLY;
    localparam int unsigned MAN_DLY =                                                                         DLY;
    // TODO: test assertions

    // TCB configurations
    localparam tcb_lite_cfg_t SUB_CFG = '{HSK: '{SUB_DLY, HLD}, BUS: '{MOD, CTL, ADR, DAT, STS}};
    localparam tcb_lite_cfg_t MAN_CFG = '{HSK: '{MAN_DLY, HLD}, BUS: '{MOD, CTL, ADR, DAT, STS}};

    // TCB interfaces
    tcb_lite_if #(SUB_CFG) tcb_sub [SUB_IFN-1:0] (.clk (clk), .rst (rst));
    tcb_lite_if #(MAN_CFG) tcb_man [MAN_IFN-1:0] (.clk (clk), .rst (rst));

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

    // DUT instances
    generate
    case (DUT)
        "ERROR": begin: error
            tcb_lite_lib_error dut (
                .sub  (tcb_sub[0]),
                .sts  ('0)
            );
        end: error
        "PASSTHROUGH": begin: passthrough
            tcb_lite_lib_passthrough dut [SUB_IFN-1:0] (
                .sub  (tcb_sub),
                .man  (tcb_man)
            );
        end: passthrough
        "REGISTER_REQUEST": begin: register_request
            tcb_lite_lib_register_request dut (
                .sub  (tcb_sub[0]),
                .man  (tcb_man[0])
            );
        end: register_request
        "REGISTER_RESPONSE": begin: register_response
            tcb_lite_lib_register_response dut (
                .sub  (tcb_sub[0]),
                .man  (tcb_man[0])
            );
        end: register_response
        "REGISTER_BACKPRESSURE": begin: register_backpressure
            tcb_lite_lib_register_backpressure dut (
                .sub  (tcb_sub[0]),
                .man  (tcb_man[0])
            );
        end: register_backpressure
        "LOGSIZE2BYTEENA_ALIGNED_FALSE": begin: logsize2byteena_aligned_false
            tcb_lite_lib_logsize2byteena #(
                .ALIGNED (1'b0)
            ) dut (
                .sub  (tcb_sub[0]),
                .man  (tcb_man[0])
            );
        end: logsize2byteena_aligned_false
        "LOGSIZE2BYTEENA_ALIGNED_TRUE": begin: logsize2byteena_aligned_true
            tcb_lite_lib_logsize2byteena #(
                .ALIGNED (1'b1)
            ) dut (
                .sub  (tcb_sub[0]),
                .man  (tcb_man[0])
            );
        end: logsize2byteena_aligned_true
        "ARBITER_MULTIPLEXER": begin: arbiter_multiplexer
            localparam bit unsigned [SUB_IFL-1:0] SUB_PRI [SUB_IFN-1:0] = '{1'd1, 1'd0};
            // select
            logic [$clog2(SUB_IFN)-1:0] sel;
            tcb_lite_lib_arbiter #(
                .IFN (SUB_IFN),
                .PRI (SUB_PRI)
            ) arb (
                .mon  (tcb_sub),
                .sel  (sel)
            );
            tcb_lite_lib_multiplexer mux (
                .sel  (sel),
                .sub  (tcb_sub),
                .man  (tcb_man[0])
            );
        end: arbiter_multiplexer
        "DECODER_DEMULTIPLEXER": begin: decoder_demultiplexer
            localparam logic [ADR-1:0] MAN_DAM [MAN_IFN-1:0] = '{{1'b0, 31'bx}, {1'b1, 31'bx}};
            logic [$clog2(MAN_IFN)-1:0] sel;
            tcb_lite_lib_decoder #(
                .IFN (MAN_IFN),
                .DAM (MAN_DAM)
            ) dec (
                .mon  (tcb_sub[0]),
                .sel  (sel)
            );
            tcb_lite_lib_demultiplexer dmx (
                .sel  (sel),
                .sub  (tcb_sub[0]),
                .man  (tcb_man)
            );
        end: decoder_demultiplexer
        "INTERCONNECT": begin: dut
            localparam bit unsigned [SUB_IFL-1:0] SUB_PRI [SUB_IFN-1:0] = '{1'd1, 1'd0};
            localparam logic [ADR-1:0] MAN_DAM [MAN_IFN-1:0] = '{{1'b0, 31'bx}, {1'b1, 31'bx}};
            tcb_lite_lib_interconnect #(
                .SUB_IFN (SUB_IFN),
                .MAN_IFN (MAN_IFN),
                .DAM     (MAN_DAM),
                .PRI     (SUB_PRI),
                .TOPOLOGY ("STAR")
            ) dut (
                .tcb_sub (tcb_sub),
                .tcb_man (tcb_man)
            );
        end: dut
        default: begin: undefined
            initial $error("DUT module '%s' not recognized.", DUT);
        end: undefined
    endcase
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

endmodule: tcb_lite_dut_wrapper
