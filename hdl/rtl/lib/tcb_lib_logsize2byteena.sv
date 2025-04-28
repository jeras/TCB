////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library log. size to byte enable mode conversion
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

module tcb_lib_logsize2byteena
  import tcb_pkg::*;
#(
  parameter bit ALIGNED = 1'b1
)(
  // interfaces
  tcb_if.sub sub,    // TCB subordinate port (manager     device connects here)
  tcb_if.man man     // TCB manager     port (subordinate device connects here)
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifndef ALTERA_RESERVED_QIS
`else
  // comparing subordinate and manager interface parameters
  initial
  begin
    tcb_phy_match_t match = '{MOD: 1'b0, default: 1'b1};
    // validate TCB PHY.MOD parameter
    assert (sub.PHY.MOD == TCB_LOG_SIZE)
      $fatal("ERROR: %m parameter (sub.PHY.MOD = %s) != TCB_LOG_SIZE", sub.PHY.MOD.name());
    assert (man.PHY.MOD == TCB_BYTE_ENA)
      $fatal("ERROR: %m parameter (sub.PHY.MOD = %s) != TCB_LOG_SIZE", man.PHY.MOD.name());
    // TCB PHY.ORD ASCENDING byte order is not supported
    assert (sub.PHY.MOD != TCB_DESCENDING)
      $fatal("ERROR: %m parameter (sub.PHY.ORD = %s) != TCB_DESCENDING", sub.PHY.ORD.name());
    // validate remaining TCB PHY parameters
    assert tcb_phy_match(sub.PHY, man.PHY, match)
      $fatal("ERROR: %m parameter (sub.PHY = %p) != (man.PHY = %p)", sub.PHY, man.PHY);
  end
`endif

// TODO: this file need a proper testbench and a serious cleanup

////////////////////////////////////////////////////////////////////////////////
// request
////////////////////////////////////////////////////////////////////////////////

  // handshake
  assign man.vld = sub.vld;

  // request
  assign man.req.cmd = sub.req.cmd;
  assign man.req.wen = sub.req.wen;
  assign man.req.ndn = sub.req.ndn;

////////////////////////////////////////////////////////////////////////////////
// write/read data
////////////////////////////////////////////////////////////////////////////////

  // request/response data packed arrays
  logic [sub.PHY_BEN-1:0][8-1:0] sub_req_wdt, sub_rsp_rdt;
  logic [man.PHY_BEN-1:0][8-1:0] man_req_wdt, man_rsp_rdt;

  // byte enable
  logic [sub.PHY_BEN-1:0]        sub_req_ben             ;

  // request/response address segment
  logic [sub.PHY_MAX-1:0]        req_off,     rsp_off;

  // request/response endianness
  logic                          req_ndn,     rsp_ndn;

////////////////////////////////////////////////////////////////////////////////
// address alignment
////////////////////////////////////////////////////////////////////////////////

  // request/response address segment
  assign req_off = sub.req_dly[0      ].adr[sub.PHY_MAX-1:0];
  assign rsp_off = sub.req_dly[sub.DLY].adr[sub.PHY_MAX-1:0];

  // mask unaligned address bits
  generate
    if (sub.PHY.ALN > 0) begin: alignment
      assign man.req.adr = {sub.req.adr[sub.PHY_ADR-1:sub.PHY.ALN], sub.PHY.ALN'('0)};
    end: alignment
    else begin
      assign man.req.adr = sub.req.adr;
    end
  endgenerate

////////////////////////////////////////////////////////////////////////////////
// multiplexers
////////////////////////////////////////////////////////////////////////////////

  // request/response endianness
  assign req_ndn = sub.req             .ndn;
  assign rsp_ndn = sub.req_dly[sub.DLY].ndn;

  // logarithmic size mode (subordinate interface) byte enable
  always_comb
  for (int unsigned i=0; i<sub.PHY_BEN; i++) begin: logsize2byteena
    sub_req_ben[i] = (i < 2**sub.req.siz) ? 1'b1 : 1'b0;
  end: logsize2byteena

  // write/read data packed array to/from vector
  assign sub_req_wdt = sub.req.wdt;
  assign sub.rsp.rdt = sub_rsp_rdt;

generate
if (ALIGNED) begin

    // byte enable
    always_comb
    begin
      case (sub.req.siz)
        0 : case (req_off)
          2'b00: man.req.ben = 4'b0001;
          2'b01: man.req.ben = 4'b0010;
          2'b10: man.req.ben = 4'b0100;
          2'b11: man.req.ben = 4'b1000;
        endcase
        1 : case (req_off[1])
          1'b0 : man.req.ben = 4'b0011;
          1'b1 : man.req.ben = 4'b1100;
        endcase
        2      : man.req.ben = 4'b1111;
        default: man.req.ben = 4'bxxxx;
      endcase
    end

//  // write access
//  always_comb
//  begin
//    case (sub.req.siz)
//      0 : case (req_off)
//        2'b00: man_req_wdt = '{0: sub_req_wdt[0], default: 'x};
//        2'b01: man_req_wdt = '{1: sub_req_wdt[0], default: 'x};
//        2'b10: man_req_wdt = '{2: sub_req_wdt[0], default: 'x};
//        2'b11: man_req_wdt = '{3: sub_req_wdt[0], default: 'x};
//      endcase
//      1 : case (req_off[1])
//        1'b0 : man_req_wdt = '{1: sub_req_wdt[1], 0: sub_req_wdt[0], default: 'x};
//        1'b1 : man_req_wdt = '{3: sub_req_wdt[1], 2: sub_req_wdt[0], default: 'x};
//      endcase
//      2      : man_req_wdt = sub_req_wdt   ;
//      default: man_req_wdt = '{default: 'x};
//    endcase
//  end

//  // read access
//  always_comb
//  begin
//    case (sub.dly[sub.DLY].siz)
//      TCB_BYTE: case (rsp_off)
//        2'b00:  sub_rsp_rdt = '{0: man_rsp_rdt[0], default: 'x};
//        2'b01:  sub_rsp_rdt = '{0: man_rsp_rdt[1], default: 'x};
//        2'b10:  sub_rsp_rdt = '{0: man_rsp_rdt[2], default: 'x};
//        2'b11:  sub_rsp_rdt = '{0: man_rsp_rdt[3], default: 'x};
//      endcase
//      TCB_HALF: case (rsp_off[1])
//        1'b0 :  sub_rsp_rdt = '{1: man_rsp_rdt[1], 0: man_rsp_rdt[0], default: 'x};
//        1'b1 :  sub_rsp_rdt = '{1: man_rsp_rdt[3], 0: man_rsp_rdt[2], default: 'x};
//      endcase
//      TCB_WORD: sub_rsp_rdt = man_rsp_rdt   ;
//      default:  sub_rsp_rdt = '{default: 'x};
//    endcase
//  end

//    // byte enable
//    assign man.req.ben = {
//      sub_req_ben[~req_off & 2'b11],
//      sub_req_ben[~req_off & 2'b10],
//      sub_req_ben[~req_off & 2'b01],
//      sub_req_ben[~req_off & 2'b00]
//    };

    // write access
    always_comb
    case (sub.req.siz)
      2'b00  : man_req_wdt = {4{sub_req_wdt[0:0]}};
      2'b01  : man_req_wdt = {2{sub_req_wdt[1:0]}};
      2'b10  : man_req_wdt = {1{sub_req_wdt[3:0]}};
      default: man_req_wdt = 'x;
    endcase


//    // read access
//    assign sub_rsp_rdt = {
//      man_rsp_rdt[          2'b11],
//      man_rsp_rdt[          2'b10],
//      man_rsp_rdt[rsp_off | 2'b01],
//      man_rsp_rdt[rsp_off | 2'b00]
//    };

    logic [4-1:0][8-1:0] tmp_dtw;  // data word
    logic [2-1:0][8-1:0] tmp_dth;  // data half
    logic [1-1:0][8-1:0] tmp_dtb;  // data byte

    // read data multiplexer
    assign tmp_dtw = man_rsp_rdt[3:0];
    assign tmp_dth = rsp_off[1] ? tmp_dtw[3:2] : tmp_dtw[1:0];
    assign tmp_dtb = rsp_off[0] ? tmp_dth[1:1] : tmp_dth[0:0];
    // read data multiplexer
    assign sub_rsp_rdt = {tmp_dtw[3:2], tmp_dth[1], tmp_dtb[0]};

  end else begin

    // byte enable
    always_comb
    for (int unsigned i=0; i<sub.PHY_BEN; i++) begin: ben
      unique case (sub.req.ndn)
        TCB_LITTLE:  man.req.ben[i] = sub_req_ben[(            (i-req_off)) % sub.PHY_BEN];
        TCB_BIG   :  man.req.ben[i] = sub_req_ben[(sub.PHY_BEN-(i-req_off)) % sub.PHY_BEN];
      endcase
    end: ben

    // write data
    always_comb
    for (int unsigned i=0; i<sub.PHY_BEN; i++) begin: wdt
      unique case (sub.req.ndn)
        TCB_LITTLE:  man_req_wdt[i] = sub_req_wdt[(            (i-req_off)) % sub.PHY_BEN];
        TCB_BIG   :  man_req_wdt[i] = sub_req_wdt[(sub.PHY_BEN-(i-req_off)) % sub.PHY_BEN];
      endcase
    end: wdt

    // read data
    always_comb
    for (int unsigned i=0; i<sub.PHY_BEN; i++) begin: rdt
      unique case (sub.req.ndn)
        TCB_LITTLE:  sub_rsp_rdt[i] = man_rsp_rdt[(            (i+rsp_off)) % sub.PHY_BEN];
        TCB_BIG   :  sub_rsp_rdt[i] = man_rsp_rdt[(sub.PHY_BEN-(i+rsp_off)) % sub.PHY_BEN];
      endcase
    end: rdt

end
endgenerate

  // write/read data packed array to/from vector
  assign man.req.wdt = man_req_wdt;
  assign man_rsp_rdt = man.rsp.rdt;

////////////////////////////////////////////////////////////////////////////////
// response
////////////////////////////////////////////////////////////////////////////////

  // error
  assign sub.rsp.sts = man.rsp.sts;

  // handshake
  assign sub.rdy = man.rdy;

endmodule: tcb_lib_logsize2byteena
