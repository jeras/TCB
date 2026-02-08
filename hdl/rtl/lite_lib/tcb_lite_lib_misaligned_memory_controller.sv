////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) library misaligned memory controller
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

module tcb_lite_lib_misaligned_memory_controller
    import tcb_lite_pkg::*;
#(
    // configuration parameters
    parameter  tcb_lite_cfg_t CFG = TCB_LITE_CFG_DEF,  // configuration parameter
    parameter  int unsigned   GRN = 1, // granularity in bytes
    // local parameters
    localparam int unsigned CFG_BUS_BYT = CFG.BUS.DAT/8,
    localparam int unsigned CFG_BUS_OFF = $clog2(CFG_BUS_BYT),
    localparam int unsigned MEM_CEN = CFG_BUS_BYT/GRN,
    localparam int unsigned MEM_ADR = CFG.BUS.ADR-CFG_BUS_OFF,
    localparam int unsigned MEM_DAT = CFG.BUS.DAT/MEM_CEN
)(
    // TCB-Lite interface
    tcb_lite_if.sub sub,  // TCB subordinate interface (manager device connects here)
    // SRAM interface
    output logic [MEM_CEN-1:0]              mem_cen,  // chip enable
    output logic                            mem_wen,  // write enable
    output logic [MEM_CEN-1:0][MEM_ADR-1:0] mem_adr,  // address
    output logic [MEM_CEN-1:0][MEM_DAT-1:0] mem_wdt,  // write data
    input  logic [MEM_CEN-1:0][MEM_DAT-1:0] mem_rdt   // read data
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    // BUS parameters
    initial begin
        // data sizing mode
        assert (sub.CFG.BUS.MOD == 1'b1) else $error("unsupported (sub.CFG.BUS.MOD = %0s) != 1'b1", sub.CFG.BUS.MOD);
        // other parameters
    end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

    // address and next address
    logic [MEM_ADR-1:0] adr;
    logic [MEM_ADR-1:0] nxt;
    // offset
    logic [CFG_BUS_OFF-1:0] off;

    assign mem_cen = {MEM_CEN{sub.vld    }}
                   &          sub.req.byt  ;
    assign mem_wen =          sub.req.wen  ;

    // address
    assign adr = sub.req.adr[CFG_BUS_OFF+:MEM_ADR];
    // offset
    assign off = sub.req.adr[CFG_BUS_OFF-1:0];

    assign nxt = adr + 1;

    // address or next address
    generate
    for (genvar i=0; i<CFG_BUS_BYT; i++) begin
         assign mem_adr[i] = (i < off) ? nxt : adr;
    end
    endgenerate

    // request/response data
    assign mem_wdt = sub.req.wdt;
    assign sub.rsp.rdt = mem_rdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

    // status error
    assign sub.rsp.sts = '0;
    assign sub.rsp.err = 1'b0;

    // handshake
    assign sub.rdy = 1'b1;

endmodule: tcb_lite_lib_misaligned_memory_controller
