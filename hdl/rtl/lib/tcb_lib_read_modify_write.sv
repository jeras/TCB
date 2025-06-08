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
    assert (sub.CFG.BUS.AMO == TCB_AMO_PRESENT) else $error("mismatch (sub.CFG.BUS.AMO = %0s) != TCB_AMO_PRESENT", sub.CFG.BUS.AMO.name());
    assert (man.CFG.BUS.AMO == TCB_AMO_ABSENT ) else $error("mismatch (man.CFG.BUS.AMO = %0s) != TCB_AMO_ABSENT" , man.CFG.BUS.AMO.name());
    // other parameters
    assert (sub.CFG.BUS.ADR == man.CFG.BUS.ADR) else $error("mismatch (sub.CFG.BUS.ADR  = %0d) != (man.CFG.BUS.ADR  = %0d)", sub.CFG.BUS.ADR       , man.CFG.BUS.ADR       );
    assert (sub.CFG.BUS.DAT == man.CFG.BUS.DAT) else $error("mismatch (sub.CFG.BUS.DAT  = %0d) != (man.CFG.BUS.DAT  = %0d)", sub.CFG.BUS.DAT       , man.CFG.BUS.DAT       );
    assert (sub.CFG.BUS.LEN == man.CFG.BUS.LEN) else $error("mismatch (sub.CFG.BUS.LEN  = %0d) != (man.CFG.BUS.LEN  = %0d)", sub.CFG.BUS.LEN       , man.CFG.BUS.LEN       );
    assert (sub.CFG.BUS.LCK == man.CFG.BUS.LCK) else $error("mismatch (sub.CFG.BUS.LCK  = %0s) != (man.CFG.BUS.LCK  = %0s)", sub.CFG.BUS.LCK.name(), man.CFG.BUS.LCK.name());
    assert (sub.CFG.BUS.CHN == man.CFG.BUS.CHN) else $error("mismatch (sub.CFG.BUS.CHN  = %0s) != (man.CFG.BUS.CHN  = %0s)", sub.CFG.BUS.CHN.name(), man.CFG.BUS.CHN.name());
    assert (sub.CFG.BUS.PRF == man.CFG.BUS.PRF) else $error("mismatch (sub.CFG.BUS.PRF  = %0s) != (man.CFG.BUS.PRF  = %0s)", sub.CFG.BUS.PRF.name(), man.CFG.BUS.PRF.name());
    assert (sub.CFG.BUS.NXT == man.CFG.BUS.NXT) else $error("mismatch (sub.CFG.BUS.NXT  = %0s) != (man.CFG.BUS.NXT  = %0s)", sub.CFG.BUS.NXT.name(), man.CFG.BUS.NXT.name());
    assert (sub.CFG.BUS.MOD == man.CFG.BUS.MOD) else $error("mismatch (sub.CFG.BUS.MOD  = %0s) != (man.CFG.BUS.MOD  = %0s)", sub.CFG.BUS.MOD.name(), man.CFG.BUS.MOD.name());
    assert (sub.CFG.BUS.ORD == man.CFG.BUS.ORD) else $error("mismatch (sub.CFG.BUS.ORD  = %0s) != (man.CFG.BUS.ORD  = %0s)", sub.CFG.BUS.ORD.name(), man.CFG.BUS.ORD.name());
    assert (sub.CFG.BUS.NDN == man.CFG.BUS.NDN) else $error("mismatch (sub.CFG.BUS.NDN  = %0s) != (man.CFG.BUS.NDN  = %0s)", sub.CFG.BUS.NDN.name(), man.CFG.BUS.NDN.name());
  end

  generate
    if (sub.CFG.BUS.CHN != TCB_CHN_READ_ONLY) begin
      initial assert ($bits(sub.req.wdt) == $bits(man.req.wdt)) else $error("mismatch ($bits(sub.req.wdt) = %0d) != ($bits(man.req.wdt) = %0d)", $bits(sub.req.wdt), $bits(man.req.wdt));
    end
    if (sub.CFG.BUS.CHN != TCB_CHN_WRITE_ONLY) begin
      initial assert ($bits(sub.rsp.rdt) == $bits(man.rsp.rdt)) else $error("mismatch ($bits(sub.rsp.rdt) = %0d) != ($bits(man.rsp.rdt) = %0d)", $bits(sub.rsp.rdt), $bits(man.rsp.rdt));
    end
  endgenerate

  // packeting parameters
  initial begin
    assert (sub.CFG.PMA.MIN == man.CFG.PMA.MIN) else $error("mismatch (sub.CFG.PMA.MIN = %0d) != (man.CFG.PMA.MIN = %0d)", sub.CFG.PMA.MIN, man.CFG.PMA.MIN);
    assert (sub.CFG.PMA.OFF == man.CFG.PMA.OFF) else $error("mismatch (sub.CFG.PMA.OFF = %0d) != (man.CFG.PMA.OFF = %0d)", sub.CFG.PMA.OFF, man.CFG.PMA.OFF);
    assert (sub.CFG.PMA.ALN == man.CFG.PMA.ALN) else $error("mismatch (sub.CFG.PMA.ALN = %0d) != (man.CFG.PMA.ALN = %0d)", sub.CFG.PMA.ALN, man.CFG.PMA.ALN);
  end

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;

  // request
  assign man.req.lck = sub.req.lck;
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
  localparam int unsigned DAT = sub.CFG.BUS.DAT;

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
