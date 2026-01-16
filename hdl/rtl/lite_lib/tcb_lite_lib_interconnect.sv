////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library interconnect
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

module tcb_lite_lib_interconnect
    import tcb_lite_pkg::*;
#(
    // interconnect parameters (subordinate/manager interface number and logarithm)
    parameter  int unsigned SUB_IFN = 2,
    parameter  int unsigned MAN_IFN = 2,
    // local parameters
    localparam int unsigned SUB_IFL = $clog2(SUB_IFN),
    localparam int unsigned MAN_IFL = $clog2(MAN_IFN),
    // arbiter priority and decoder address map
    parameter  bit unsigned [SUB_IFL-1:0] PRI [SUB_IFN-1:0],
    parameter  logic [32-1:0] DAM [MAN_IFN-1:0],
    // topology
    parameter  string TOPOLOGY = "STAR"  // "STAR", "MESH"
)(
    // TCB interfaces
    tcb_lite_if.sub tcb_sub [SUB_IFN-1:0],  // TCB subordinate interfaces (manager     devices connect here)
    tcb_lite_if.man tcb_man [MAN_IFN-1:0]  // TCB manager     interface  (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////
/*
`ifdef ALTERA_RESERVED_QIS
`else
    // camparing subordinate and manager interface parameters
    generate
    for (genvar i=0; i<IFN; i++) begin: param
        initial begin
            assert (man.DLY == sub[i].DLY) else $error("Parameter (man.DLY = %p) != (sub[%0d].DLY = %p)", man.DLY, i, sub[i].DLY);
            assert (man.DAT == sub[i].DAT) else $error("Parameter (man.DAT = %p) != (sub[%0d].DAT = %p)", man.DAT, i, sub[i].DAT);
            assert (man.ADR == sub[i].ADR) else $error("Parameter (man.ADR = %p) != (sub[%0d].ADR = %p)", man.ADR, i, sub[i].ADR);
            assert (man.MSK == sub[i].MSK) else $error("Parameter (man.MSK = %p) != (sub[%0d].MSK = %p)", man.MSK, i, sub[i].MSK);
            assert (man.MOD == sub[i].MOD) else $error("Parameter (man.MOD = %p) != (sub[%0d].MOD = %p)", man.MOD, i, sub[i].MOD);
        end
    end: param
    endgenerate
`endif
*/
////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// STAR topology
////////////////////////////////////////////////////////////////////////////////

    generate
    case (TOPOLOGY)
        "STAR": begin: star

            // TCB interfaces
            tcb_lite_if #(tcb_sub[0].CFG) star_tcb_man (.clk (tcb_sub[0].clk), .rst (tcb_sub[0].rst));
            tcb_lite_if #(tcb_sub[0].CFG) star_tcb_sub (.clk (tcb_sub[0].clk), .rst (tcb_sub[0].rst));

            // control
            logic [SUB_IFL-1:0] arb_sel;  // arbiter select
            logic [MAN_IFL-1:0] dec_sel;  // decoder select

            // RTL arbiter
            tcb_lite_lib_arbiter #(
                // arbitration priority mode
                //.MD   (),
                // interconnect parameters
                .IFN  (SUB_IFN)
                // interface priorities (lower number is higher priority)
                //.PRI  (PRI)
            ) star_arb (
                .mon  (tcb_sub),
                .sel  (arb_sel)
            );
        
            // RTL multiplexer
            tcb_lite_lib_multiplexer #(
                // interconnect parameters
                .IFN   (SUB_IFN)
            ) star_mux (
                // control
                .sel  (arb_sel),
                // TCB interfaces
                .sub  (tcb_sub),
                .man  (star_tcb_man)
            );

            // RTL decoder
            tcb_lite_lib_decoder #(
                // interconnect parameters
                .IFN  (MAN_IFN),
                // decoder address and mask array
                .DAM  (DAM)
            ) star_dec (
                .mon  (star_tcb_sub),
                .sel  (dec_sel)
            );
        
            // RTL demultiplexer
            tcb_lite_lib_demultiplexer #(
                // interconnect parameters
                .IFN   (MAN_IFN)
            ) star_dmx (
                // control
                .sel  (dec_sel),
                // TCB interfaces
                .sub  (star_tcb_sub),
                .man  (tcb_man)
            );

        end: star
        default: begin
            $error("Topology '%s' is not supported.");
        end
    endcase
endgenerate


endmodule: tcb_lite_lib_interconnect
