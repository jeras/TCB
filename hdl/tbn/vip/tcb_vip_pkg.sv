////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) transaction PacKaGe
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

package tcb_vip_pkg;

  import tcb_pkg::*;
  import tcb_vip_transfer_pkg::*;
  export tcb_vip_transfer_pkg::*;
  import tcb_vip_transaction_pkg::*;
  export tcb_vip_transaction_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// TCB class
////////////////////////////////////////////////////////////////////////////////

  class tcb_vip_c #(
    parameter       tcb_phy_t PHY = TCB_PAR_PHY_DEF,
    parameter  type tcb_req_cmd_t = tcb_req_cmd_def_t,
    parameter  type tcb_rsp_sts_t = tcb_rsp_sts_def_t
  ) extends tcb_vip_transaction_c #(
    .PHY           (PHY),
    .tcb_req_cmd_t (tcb_req_cmd_t),
    .tcb_rsp_sts_t (tcb_rsp_sts_t)
  );

////////////////////////////////////////////////////////////////////////////////
// write/read/check
////////////////////////////////////////////////////////////////////////////////

    task write8 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [1-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [1-1:0][PHY.UNT-1:0] rdt;
      transaction8(1'b1, adr, wdt, rdt, sts);
    endtask: write8

    task read8 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [1-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [1-1:0][PHY.UNT-1:0] wdt = 'x;
      transaction8(1'b0, adr, wdt, rdt, sts);
    endtask: read8

    task check8 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [1-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [1-1:0][PHY.UNT-1:0] tmp_wdt = 'x;
      logic [1-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                      tmp_sts;
      transaction8(1'b0, adr, tmp_wdt, tmp_rdt, tmp_sts);
      if (tmp_rdt !== rdt) $display("ERROR: %m: (rdt=8'h%2X) !== (dat=8'h%2X) mismatch.", tmp_rdt, rdt);
      if (tmp_sts !== sts) $display("ERROR: %m: (sts=1'b%1b) !== (sts=1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check8

    task write16 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [2-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [2-1:0][PHY.UNT-1:0] rdt;
      transaction16(1'b1, adr, wdt, rdt, sts);
    endtask: write16

    task read16 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [2-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [4-1:0][PHY.UNT-1:0] wdt = 'x;
      transaction16(1'b0, adr, wdt, rdt, sts);
    endtask: read16

    task check16 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [2-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [2-1:0][PHY.UNT-1:0] tmp_wdt = 'x;
      logic [2-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                      tmp_sts;
      transaction16(1'b0, adr, tmp_wdt, tmp_rdt, tmp_sts);
      if (tmp_rdt !== rdt) $display("ERROR: %m: (rdt=16'h%4X) !== ref(rdt=16'h%4X) mismatch.", tmp_rdt, rdt);
      if (tmp_sts !== sts) $display("ERROR: %m: (sts= 1'b%1b) !== ref(sts= 1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check16

    task write32 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [4-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [4-1:0][PHY.UNT-1:0] rdt;
      transaction32(1'b1, adr, wdt, rdt, sts);
    endtask: write32

    task read32 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [4-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [4-1:0][PHY.UNT-1:0] wdt = 'x;
      transaction32(1'b0, adr, wdt, rdt, sts);
    endtask: read32

    task check32 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [4-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [4-1:0][PHY.UNT-1:0] tmp_wdt = 'x;
      logic [4-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                      tmp_sts;
      transaction32(1'b0, adr, tmp_wdt, tmp_rdt, tmp_sts);
      if (tmp_rdt !== rdt) $display("ERROR: %m: (rdt=32'h%8X) !== ref(rdt=32'h%8X) mismatch.", tmp_rdt, rdt);
      if (tmp_sts !== sts) $display("ERROR: %m: (sts= 1'b%1b) !== ref(sts= 1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check32

    task write64 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [8-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [8-1:0][PHY.UNT-1:0] rdt;
      transaction64(1'b1, adr, wdt, rdt, sts);
    endtask: write64

    task read64 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [8-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [8-1:0][PHY.UNT-1:0] wdt = 'x;
      transaction64(1'b0, adr, wdt, rdt, sts);
    endtask: read64

    task check64 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [8-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [8-1:0][PHY.UNT-1:0] tmp_wdt = 'x;
      logic [8-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                      tmp_sts;
      transaction64(1'b0, adr, tmp_wdt, tmp_rdt, tmp_sts);
      if (tmp_rdt !== rdt) $display("ERROR: %m: (rdt=64'h%16X) !== (dat=64'h%16X) mismatch.", tmp_rdt, rdt);
      if (tmp_sts !== sts) $display("ERROR: %m: (sts= 1'b%01b) !== (sts= 1'b%01b) mismatch.", tmp_sts, sts);
    endtask: check64

    task write128 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic [16-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [16-1:0][PHY.UNT-1:0] rdt;
      transaction128(1'b1, adr, wdt, rdt, sts);
    endtask: write128

    task read128 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic [16-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [16-1:0][PHY.UNT-1:0] wdt = 'x;
      transaction128(1'b0, adr, wdt, rdt, sts);
    endtask: read128

    task check128 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic [16-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [16-1:0][PHY.UNT-1:0] tmp_wdt = 'x;
      logic [16-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                       tmp_sts;
      transaction128(1'b0, adr, tmp_wdt, tmp_rdt, tmp_sts);
      if (tmp_rdt !== rdt) $display("ERROR: %m: (rdt=128'h%32X) !== (dat=128'h%32X) mismatch.", tmp_rdt, rdt);
      if (tmp_sts !== sts) $display("ERROR: %m: (sts=  1'b%01b) !== (sts=  1'b%01b) mismatch.", tmp_sts, sts);
    endtask: check128

  endclass: tcb_vip_c

endpackage: tcb_vip_pkg
