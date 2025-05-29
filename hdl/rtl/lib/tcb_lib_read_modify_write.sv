////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library: read modify write
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

module tcb_lib_read_modify_write
  import tcb_pkg::*;
(
  // interfaces
  tcb_if.sub sub,    // TCB subordinate interface (manager     device connects here)
  tcb_if.man man     // TCB manager     interface (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

  // BUS parameters
  initial begin
    // AMO configuration
    assert (sub.BUS.AMO == TCB_AMO_ENABLED ) else $error("mismatch (sub.BUS.AMO = %0s) != TCB_AMO_ENABLED ", sub.BUS.AMO.name());
    assert (man.BUS.AMO == TCB_AMO_DISABLED) else $error("mismatch (man.BUS.AMO = %0s) != TCB_AMO_DISABLED", man.BUS.AMO.name());
    // other parameters
    assert (sub.BUS.ADR == man.BUS.ADR) else $error("mismatch (sub.BUS.ADR  = %0d) != (man.BUS.ADR  = %0d)", sub.BUS.ADR       , man.BUS.ADR       );
    assert (sub.BUS.DAT == man.BUS.DAT) else $error("mismatch (sub.BUS.DAT  = %0d) != (man.BUS.DAT  = %0d)", sub.BUS.DAT       , man.BUS.DAT       );
    assert (sub.BUS.FRM == man.BUS.FRM) else $error("mismatch (sub.BUS.FRM  = %0d) != (man.BUS.FRM  = %0d)", sub.BUS.FRM       , man.BUS.FRM       );
    assert (sub.BUS.CHN == man.BUS.CHN) else $error("mismatch (sub.BUS.CHN  = %0s) != (man.BUS.CHN  = %0s)", sub.BUS.CHN.name(), man.BUS.CHN.name());
    assert (sub.BUS.PRF == man.BUS.PRF) else $error("mismatch (sub.BUS.PRF  = %0s) != (man.BUS.PRF  = %0s)", sub.BUS.PRF.name(), man.BUS.PRF.name());
    assert (sub.BUS.NXT == man.BUS.NXT) else $error("mismatch (sub.BUS.NXT  = %0s) != (man.BUS.NXT  = %0s)", sub.BUS.NXT.name(), man.BUS.NXT.name());
    assert (sub.BUS.MOD == man.BUS.MOD) else $error("mismatch (sub.BUS.MOD  = %0s) != (man.BUS.MOD  = %0s)", sub.BUS.MOD.name(), man.BUS.MOD.name());
    assert (sub.BUS.ORD == man.BUS.ORD) else $error("mismatch (sub.BUS.ORD  = %0s) != (man.BUS.ORD  = %0s)", sub.BUS.ORD.name(), man.BUS.ORD.name());
    assert (sub.BUS.NDN == man.BUS.NDN) else $error("mismatch (sub.BUS.NDN  = %0s) != (man.BUS.NDN  = %0s)", sub.BUS.NDN.name(), man.BUS.NDN.name());
  end

  generate
    if (sub.BUS.CHN != TCB_CHN_READ_ONLY) begin
      initial assert ($bits(sub.req.wdt) == $bits(man.req.wdt)) else $error("mismatch ($bits(sub.req.wdt) = %0d) != ($bits(man.req.wdt) = %0d)", $bits(sub.req.wdt), $bits(man.req.wdt));
    end
    if (sub.BUS.CHN != TCB_CHN_WRITE_ONLY) begin
      initial assert ($bits(sub.rsp.rdt) == $bits(man.rsp.rdt)) else $error("mismatch ($bits(sub.rsp.rdt) = %0d) != ($bits(man.rsp.rdt) = %0d)", $bits(sub.rsp.rdt), $bits(man.rsp.rdt));
    end
  endgenerate

  // packeting parameters
  initial begin
    assert (sub.PCK.MIN == man.PCK.MIN) else $error("mismatch (sub.PCK.MIN = %0d) != (man.PCK.MIN = %0d)", sub.PCK.MIN, man.PCK.MIN);
    assert (sub.PCK.OFF == man.PCK.OFF) else $error("mismatch (sub.PCK.OFF = %0d) != (man.PCK.OFF = %0d)", sub.PCK.OFF, man.PCK.OFF);
    assert (sub.PCK.ALN == man.PCK.ALN) else $error("mismatch (sub.PCK.ALN = %0d) != (man.PCK.ALN = %0d)", sub.PCK.ALN, man.PCK.ALN);
  end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;

  // request
  assign man.req.frm = sub.req.frm;
  assign man.req.len = sub.req.len;
  assign man.req.wen = sub.req.wen;
  assign man.req.ren = sub.req.ren;
  assign man.req.rpt = sub.req.rpt;
  assign man.req.inc = sub.req.inc;
  assign man.req.adr = sub.req.adr;
  assign man.req.nxt = sub.req.nxt;
  assign man.req.ndn = sub.req.ndn;

////////////////////////////////////////////////////////////////////////////////
// local parameters and functions
////////////////////////////////////////////////////////////////////////////////

  // shorthand for data bus width
  localparam int unsigned DAT = sub.BUS.DAT;

  // AMO logical functions
  function automatic logic [DAT-1:0] amo_log (
    input logic [DAT-1:0] wdt,  // write data
    input logic [DAT-1:0] rdt,  // read  data
    input logic   [5-1:0] aof   // atomic operation function
  );
    case (aof)
      AMOXOR : amo_log = wdt | rdt;
      AMOAND : amo_log = wdt & rdt;
      AMOOR  : amo_log = wdt ^ rdt;
      default: amo_log = 'x;
    endcase
  endfunction: amo_log

  // AMO arithmetic functions
  function automatic logic [DAT-1:0] amo_art (
    input logic [DAT-1:0] wdt,  // write data
    input logic [DAT-1:0] rdt,  // read  data
    input logic   [5-1:0] aof   // atomic operation function
  );
    logic           inv;  // operand inversion
    logic           uns;  // operand unsigned
    logic [DAT-1:0] op1;  // operand 1
    logic [DAT-1:0] op2;  // operand 2
    logic [DAT-0:0] sum;  // summation result
    logic           sgn;  // summation sign

    // TODO: inversion could be applied to the other operand to improve timing
    op1 =       wdt       ;
    op2 = inv ? rdt : ~rdt;
    sum = op1 + op2 + inv;

    // summation sign
    sgn = uns ? sum[DAT] : sum[DAT] ^ op1[DAT-1] ^ op2[DAT-1] ^ ~inv;

    case (aof)
      AMOADD : begin  inv = 1'b0;  uns = 1'bx;  amo_art =  sum            ;  end
      AMOMIN : begin  inv = 1'b1;  uns = 1'b0;  amo_art =  sgn ? wdt : rdt;  end
      AMOMAX : begin  inv = 1'b1;  uns = 1'b0;  amo_art = ~sgn ? wdt : rdt;  end
      AMOMINU: begin  inv = 1'b1;  uns = 1'b1;  amo_art =  sgn ? wdt : rdt;  end
      AMOMAXU: begin  inv = 1'b1;  uns = 1'b1;  amo_art = ~sgn ? wdt : rdt;  end
      default: begin  inv = 1'bx;  uns = 1'bx;  amo_art =  'x             ;  end
    endcase
  endfunction: amo_art

////////////////////////////////////////////////////////////////////////////////
// data paths
////////////////////////////////////////////////////////////////////////////////

  // write data path
  always_comb
  case (sub.req.amo)
    AMOSWAP: man.req.wdt = sub.req.wdt;
    AMOXOR ,
    AMOAND ,
    AMOOR  : man.req.wdt = amo_log(sub.req.wdt, man.rsp.rdt, sub.req.amo);
    AMOADD ,
    AMOMIN ,
    AMOMAX ,
    AMOMINU,
    AMOMAXU: man.req.wdt = amo_art(sub.req.wdt, man.rsp.rdt, sub.req.amo);
    default: man.req.wdt = 'x;
  endcase

  // read data path
  assign sub.rsp.rdt = man.rsp.rdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // status error
  assign sub.rsp.sts = man.rsp.sts;

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_read_modify_write
