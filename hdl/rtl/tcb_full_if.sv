////////////////////////////////////////////////////////////////////////////////
// TCB-Full (Tightly Coupled Bus) SystemVerilog interface
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

interface tcb_full_if
    import tcb_full_pkg::*;
#(
    // configuration parameters
    parameter  type cfg_t = tcb_cfg_t,   // configuration parameter type
    parameter  cfg_t CFG = TCB_CFG_DEF,  // configuration parameter
    // request/response structure types
    parameter  type req_t = tcb_req_t,   // request
    parameter  type rsp_t = tcb_rsp_t,   // response
    // VIP (not to be used in RTL)
    parameter  type vip_t = tcb_vip_t,   // VIP parameter type
    parameter  vip_t VIP = TCB_VIP_DEF,  // VIP parameter
    // partial address decoding mask
    parameter  logic [CFG.BUS.ADR-1:0] MSK = '1
)(
    // system signals
    input  logic clk,  // clock
    input  logic rst   // reset
);

////////////////////////////////////////////////////////////////////////////////
// I/O ports
////////////////////////////////////////////////////////////////////////////////

    // handshake
    logic vld;  // valid
    logic rdy;  // ready

    // request/response
    req_t req;  // request
    rsp_t rsp;  // response

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

    generate
        // framing lock (maximum frame length is FRM+1)
        if (CFG.BUS.LCK > 0) begin
            // check frame enable bit presence and type
            initial assert ($bits(req.lck) == 1) else
                $error("unexpected type(req.lck) = ", $typename(req.lck));
            // check frame length vector presence and size
            initial assert ($bits(req.len) == $clog2(CFG.BUS.LEN)) else
                $error("unexpected type(req.len) = ", $typename(req.len));
        end
        // channel
        if (CFG.BUS.CHN == TCB_CHN_FULL_DUPLEX) begin
            // read enable signal must be present on full duplex channels
            initial assert ($bits(req.ren) == 1) else
                $error("unexpected type(req.ren) = ", $typename(req.ren));
        end
        // channel
        if (CFG.BUS.AMO == TCB_AMO_PRESENT) begin
            // atomic enable signal must be present for AMO support
            initial assert ($bits(req.aen) == 1) else
                $error("unexpected type(req.aen) = ", $typename(req.ren));
            // atomic function signal must be present for AMO support
            initial assert ($bits(req.amo) == 5) else
                $error("unexpected type(req.amo) = ", $typename(req.amo));
        end
        // prefetch
        if (CFG.BUS.PRF == TCB_PRF_PRESENT) begin
            // prefetch signals rpt/inc must be present
            initial assert ($bits(req.rpt) == 1) else
                $error("unexpected type(req.rpt) = ", $typename(req.rpt));
            initial assert ($bits(req.inc) == 1) else
                $error("unexpected type(req.inc) = ", $typename(req.inc));
        end
        // address and next address
        initial assert ($bits(req.adr) > 0) else
            $error("unexpected type(req.adr) = ", $typename(req.adr));
        if (CFG.BUS.NXT == TCB_NXT_PRESENT) begin
            initial assert ($bits(req.adr) == $bits(req.nxt)) else
                $error("unexpected type(req.nxt) = ", $typename(req.nxt));
        end
        // request/write data bus and data sizing
        if (CFG.BUS.CHN != TCB_CHN_READ_ONLY) begin
            // check request/write data bus (multiple of 8 and power of 2)
            initial assert (($bits(req.wdt)%8 == 0) && ($bits(req.wdt) == 2**$clog2($bits(req.wdt)))) else
                $error("unexpected type(req.wdt) = ", $typename(req.wdt));
            // check data sizing
            case (CFG.BUS.MOD)
                TCB_MOD_LOG_SIZE: begin  // logarithmic size
                    initial assert ($bits(req.siz) == $clog2($clog2($bits(req.wdt)/8)+1)) else
                        $error("unexpected type(req.siz) = ", $typename(req.siz));
                end
                TCB_MOD_BYTE_ENA: begin  // byte enable
                    initial assert ($bits(req.byt) == $bits(req.wdt)/8) else
                        $error("unexpected type(req.byt) = ", $typename(req.byt));
                end
            endcase
        end
        // response/read data bus and data sizing
        if (CFG.BUS.CHN != TCB_CHN_READ_ONLY) begin
            // check response/read data bus (multiple of 8 and power of 2)
            initial assert (($bits(rsp.rdt)%8 == 0) && ($bits(rsp.rdt) == 2**$clog2($bits(rsp.rdt)))) else
                $error("unexpected type(rsp.rdt) = ", $typename(rsp.rdt));
            // check data sizing
            case (CFG.BUS.MOD)
                TCB_MOD_LOG_SIZE: begin  // logarithmic size
                    initial assert ($bits(req.siz) == $clog2($clog2($bits(rsp.rdt)/8)+1)) else
                        $error("unexpected type(req.siz) = ", $typename(req.siz));
                end
                TCB_MOD_BYTE_ENA: begin  // byte enable
                    initial assert ($bits(req.byt) == $bits(rsp.rdt)/8) else
                        $error("unexpected type(req.byt) = ", $typename(req.byt));
                end
            endcase
        end
        // endianness
        if (CFG.BUS.NDN == TCB_NDN_BI_NDN) begin
            // bi-endian signal presence
            initial assert ($bits(req.ndn) == 1) else
                $error("unexpected type(req.ndn) = ", $typename(req.ndn));
        end
    endgenerate

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

    // local parameters are calculated from the request
    localparam int unsigned CFG_BUS_BYT = CFG.BUS.DAT/8;
    localparam int unsigned CFG_BUS_MAX = $clog2(CFG_BUS_BYT);
    localparam int unsigned CFG_BUS_SIZ = $clog2(CFG_BUS_MAX+1);

////////////////////////////////////////////////////////////////////////////////
// helper functions
////////////////////////////////////////////////////////////////////////////////

    // TODO: rethink this functionality
    // logarithmic size mode (subordinate interface) byte enable
    function automatic logic [CFG_BUS_BYT-1:0] logsize2byteena (
        input logic [CFG_BUS_SIZ-1:0] siz
    );
        for (int unsigned i=0; i<CFG_BUS_BYT; i++) begin
            logsize2byteena[i] = (i < 2**siz) ? 1'b1 : 1'b0;
        end
    endfunction: logsize2byteena

    // write enable
    function automatic logic write (
        input logic wen
    );
        case (CFG.BUS.CHN)
            TCB_CHN_HALF_DUPLEX:  write =  wen;
            TCB_CHN_FULL_DUPLEX:  write =  wen;
            TCB_CHN_WRITE_ONLY :  write = 1'b1;
            TCB_CHN_READ_ONLY  :  write = 1'b0;
        endcase
    endfunction: write

    // read enable
    function automatic logic read (
        input logic wen,
        input logic ren
    );
        case (CFG.BUS.CHN)
            TCB_CHN_HALF_DUPLEX:  read = ~wen;
            TCB_CHN_FULL_DUPLEX:  read =  ren;
            TCB_CHN_WRITE_ONLY :  read = 1'b0;
            TCB_CHN_READ_ONLY  :  read = 1'b1;
        endcase
    endfunction: read

////////////////////////////////////////////////////////////////////////////////
// transaction handshake and misalignment logic
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

    logic trn_dly [0:CFG.HSK.DLY];
    req_t req_dly [0:CFG.HSK.DLY];
    rsp_t rsp_dly [0:CFG.HSK.DLY];

    // continuous assignment
    assign trn_dly[0] = trn;
    assign req_dly[0] = req;
//  assign rsp_dly[0] = rsp;  // response assigned by VIP

    generate
        // delay line
        for (genvar i=1; i<=CFG.HSK.DLY; i++) begin: dly
            logic trn_tmp;
            req_t req_tmp;
            rsp_t rsp_tmp;
            // continuous assignment
            assign trn_dly[i] = trn_tmp;
            assign req_dly[i] = req_tmp;
            assign rsp_dly[i] = rsp_tmp;
            // propagate through delay line
            always_ff @(posedge clk)
            begin
                                  trn_tmp <= trn_dly[i-1];
                if (trn_dly[i-1]) req_tmp <= req_dly[i-1];
                if (trn_dly[i-1]) rsp_tmp <= rsp_dly[i-1];
            end
        end: dly

        if (VIP.DRV) begin: vip
            // continuous assignment
            if (CFG.HSK.DLY == 0) begin
                assign rsp = trn ? rsp_dly[CFG.HSK.DLY] : '{default: 'z};
            end else begin
                if (CFG.HSK.HLD) begin
                    assign rsp =                        rsp_dly[CFG.HSK.DLY];
                end else begin
                    assign rsp = trn_dly[CFG.HSK.DLY] ? rsp_dly[CFG.HSK.DLY] : '{default: 'x};
                end
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
        // delayed request/response
        input  trn_dly,
        input  req_dly,
        input  rsp_dly,
        // functions
        import write, read
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
        // delayed request/response
        input  trn_dly,
        input  req_dly,
        input  rsp_dly,
        // functions
        import write, read
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
        // delayed request/response
        input  trn_dly,
        input  req_dly,
        input  rsp_dly,
        // functions
        import write, read
    );

endinterface: tcb_full_if
