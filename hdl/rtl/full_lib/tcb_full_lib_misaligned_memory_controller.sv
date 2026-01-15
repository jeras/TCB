////////////////////////////////////////////////////////////////////////////////
// TCB-Full (Tightly Coupled Bus) library log. size to byte enable mode conversion
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

module tcb_full_lib_misaligned_memory_controller
    import tcb_full_pkg::*;
#(
    // configuration parameters
    parameter  type cfg_t = tcb_cfg_t,   // configuration parameter type
    parameter  cfg_t CFG = TCB_CFG_DEF,  // configuration parameter
    // local parameters
    localparam int unsigned CFG_BUS_BYT = CFG.BUS.DAT/8,
    localparam int unsigned CFG_BUS_MAX = $clog2(CFG_BUS_BYT),
    localparam int unsigned MEM_CEN = CFG_BUS_BYT/(2**CFG.PMA.OFF),
    localparam int unsigned MEM_ADR = CFG.BUS.ADR-CFG_BUS_MAX,
    localparam int unsigned MEM_DAT = CFG.BUS.DAT/MEM_CEN
    // byte order
    // TODO
)(
    // TCB interface
    tcb_full_if.sub tcb,  // TCB subordinate interface (manager device connects here)
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
        // channel configuration
        assert (tcb.CFG.BUS.CHN != TCB_CHN_FULL_DUPLEX) else $error("unsupported (tcb.CFG.BUS.CHN = %0s) == TCB_CHN_FULL_DUPLEX", tcb.CFG.BUS.CHN.name());
        // data sizing mode
        assert (tcb.CFG.BUS.MOD == TCB_MOD_BYTE_ENA)    else $error("unsupported (tcb.CFG.BUS.MOD = %0s) != TCB_MOD_BYTE_ENA", tcb.CFG.BUS.MOD.name());
        // other parameters
//        assert (      sub.BUS.FRM  ==       man.BUS.FRM ) else $error("mismatch (      sub.BUS.FRM  = %0d) != (      man.BUS.FRM  = %0d)",       sub.BUS.FRM       ,       man.BUS.FRM       );
//        assert (      sub.BUS.PRF  ==       man.BUS.PRF ) else $error("mismatch (      sub.BUS.PRF  = %0s) != (      man.BUS.PRF  = %0s)",       sub.BUS.PRF.name(),       man.BUS.PRF.name());
//        assert ($bits(sub.req.adr) == $bits(man.req.adr)) else $error("mismatch ($bits(sub.req.adr) = %0d) != ($bits(man.req.adr) = %0d)", $bits(sub.req.adr)      , $bits(man.req.adr)      );
//        assert (      sub.BUS.NXT  ==       man.BUS.NXT ) else $error("mismatch (      sub.BUS.NXT  = %0s) != (      man.BUS.NXT  = %0s)",       sub.BUS.NXT.name(),       man.BUS.NXT.name());
//        assert (      sub.BUS.ORD  ==       man.BUS.ORD ) else $error("mismatch (      sub.BUS.ORD  = %0s) != (      man.BUS.ORD  = %0s)",       sub.BUS.ORD.name(),       man.BUS.ORD.name());
//        assert (      sub.BUS.NDN  ==       man.BUS.NDN ) else $error("mismatch (      sub.BUS.NDN  = %0s) != (      man.BUS.NDN  = %0s)",       sub.BUS.NDN.name(),       man.BUS.NDN.name());
    end


//    // packeting parameters
//    initial begin
//        assert (sub.PMA.MIN == man.PMA.MIN) else $error("mismatch (sub.PMA.MIN = %0d) != (man.PMA.MIN = %0d)", sub.PMA.MIN, man.PMA.MIN);
//        assert (sub.PMA.OFF == man.PMA.OFF) else $error("mismatch (sub.PMA.OFF = %0d) != (man.PMA.OFF = %0d)", sub.PMA.OFF, man.PMA.OFF);
//        assert (sub.PMA.ALN == man.PMA.ALN) else $error("mismatch (sub.PMA.ALN = %0d) != (man.PMA.ALN = %0d)", sub.PMA.ALN, man.PMA.ALN);
//    end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

//    // request
//    generate
//        // channel
//        if (man.BUS.CHN inside {TCB_CHN_FULL_DUPLEX, TCB_CHN_HALF_DUPLEX}) begin
//            assign man.req.wen = sub.req.wen;
//        end
//        if (man.BUS.CHN inside {TCB_CHN_FULL_DUPLEX}) begin
//            assign man.req.ren = sub.req.ren;
//        end
//        // prefetch
//        if (man.BUS.PRF == TCB_PRF_PRESENT) begin
//            assign man.req.rpt = sub.req.rpt;
//            assign man.req.inc = sub.req.inc;
//        end

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

//    // request/response address offset, logarithmic size
//    logic [sub.CFG_BUS_MAX-1:0] req_off, rsp_off;
//    logic [sub.BUS_SIZ-1:0] req_siz, rsp_siz;
//
//    // endianness
//    logic                   req_ndn, rsp_ndn;
//
//    // prefix OR operation
//    function automatic [sub.CFG_BUS_MAX-1:0] prefix_or (
//        input logic [sub.CFG_BUS_MAX-1:0] val
//    );
//        prefix_or[sub.CFG_BUS_MAX-1] = val[sub.CFG_BUS_MAX-1];
//        for (int unsigned i=sub.CFG_BUS_MAX-1; i>0; i--) begin
//            prefix_or[i-1] = prefix_or[i] | val[i-1];
//        end
//    endfunction: prefix_or
//
//    // request/response address offset, logarithmic size
//    assign req_off = sub.req_dly[0          ].adr[sub.CFG_BUS_MAX-1:0];
//    assign rsp_off = sub.req_dly[sub.HSK.DLY].adr[sub.CFG_BUS_MAX-1:0];
//    assign req_siz = sub.req_dly[0          ].siz;
//    assign rsp_siz = sub.req_dly[sub.HSK.DLY].siz;

////////////////////////////////////////////////////////////////////////////////
// multiplexers
////////////////////////////////////////////////////////////////////////////////

    // address and next address
    logic [MEM_ADR-1:0] adr;
    logic [MEM_ADR-1:0] nxt;
    // offset
    logic [CFG_BUS_MAX-1:0] off;

    assign mem_cen = {MEM_CEN{tcb.vld    }}
                   &          tcb.req.byt  ;
    assign mem_wen =          tcb.req.wen  ;

    // address
    assign adr = tcb.req.adr[CFG_BUS_MAX+:MEM_ADR];
    // offset
    assign off = tcb.req.adr[CFG_BUS_MAX-1:0];

    generate
        // next address
        if (tcb.CFG.BUS.NXT == TCB_NXT_PRESENT) begin
            assign nxt = tcb.req.nxt[CFG_BUS_MAX+:MEM_ADR];
        end else begin
            assign nxt = adr + 1;
        end

        // address or next address
        for (genvar i=0; i<CFG_BUS_BYT; i++) begin
             assign mem_adr[i] = (i < off) ? nxt : adr;
        end
    endgenerate

    // request/response data
    generate
        if (tcb.CFG.BUS.CHN != TCB_CHN_READ_ONLY) begin
            assign mem_wdt = tcb.req.wdt;
        end
        if (tcb.CFG.BUS.CHN != TCB_CHN_WRITE_ONLY) begin
            assign tcb.rsp.rdt = mem_rdt;
        end
    endgenerate

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

    // status error
    assign tcb.rsp.sts = '0;

    // handshake
    assign tcb.rdy = 1'b1;

endmodule: tcb_full_lib_misaligned_memory_controller
