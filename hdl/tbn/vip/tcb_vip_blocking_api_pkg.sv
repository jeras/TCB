////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) blocking API PacKaGe
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

package tcb_vip_blocking_api_pkg;

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

    //constructor
    function new(
      input string DIR = "MON",
      input tcb_vif_t tcb
    );
      super.new(
        .DIR (DIR),
        .tcb (tcb)
      );
    endfunction: new

  //////////////////////////////////////////////////////////////////////////////
  // write/read/check
  //////////////////////////////////////////////////////////////////////////////

    task write8 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [1-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [PHY.UNT-1:0] tmp_wdt [] = new[1];
      logic [PHY.UNT-1:0] tmp_rdt [] = new[1];
      tmp_wdt = {<<PHY.UNT{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(1'b1, adr, tmp_wdt, tmp_rdt, sts);
    endtask: write8

    task read8 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [1-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [PHY.UNT-1:0] tmp_wdt [] = new[1]('{default: 'x});
      logic [PHY.UNT-1:0] tmp_rdt [] = new[1];
      transaction(1'b0, adr, tmp_wdt, tmp_rdt, sts);
      rdt = type(rdt)'({<<PHY.UNT{tmp_rdt[0:1-1]}});  // crop and reverse byte order
    endtask: read8

    task check8 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [1-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic  [1-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                       tmp_sts;
      read8(adr, tmp_rdt, tmp_sts);
      assert (tmp_rdt == rdt) else $error("(rdt=8'h%2x) !== (dat=8'h%2x) mismatch.", tmp_rdt, rdt);
      assert (tmp_sts == sts) else $error("(sts=1'b%1b) !== (sts=1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check8

    task write16 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [2-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [PHY.UNT-1:0] tmp_wdt [] = new[2]('{default: 'x});
      logic [PHY.UNT-1:0] tmp_rdt [] = new[2];
      tmp_wdt = {<<PHY.UNT{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(1'b1, adr, tmp_wdt, tmp_rdt, sts);
    endtask: write16

    task read16 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [2-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [PHY.UNT-1:0] tmp_wdt [] = new[2]('{default: 'x});
      logic [PHY.UNT-1:0] tmp_rdt [] = new[2];
      transaction(1'b0, adr, tmp_wdt, tmp_rdt, sts);
      rdt = type(rdt)'({<<PHY.UNT{tmp_rdt[0:2-1]}});  // crop and reverse byte order
    endtask: read16

    task check16 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [2-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic  [2-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                       tmp_sts;
      read16(adr, tmp_rdt, tmp_sts);
      assert (tmp_rdt == rdt) else $error("(rdt=16'h%4x) !== (dat=16'h%4x) mismatch.", tmp_rdt, rdt);
      assert (tmp_sts == sts) else $error("(sts= 1'b%1b) !== (sts= 1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check16

    task write32 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [4-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [PHY.UNT-1:0] tmp_wdt [] = new[4]('{default: 'x});
      logic [PHY.UNT-1:0] tmp_rdt [] = new[4];
      tmp_wdt = {<<PHY.UNT{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(1'b1, adr, tmp_wdt, tmp_rdt, sts);
    endtask: write32

    task read32 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [4-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [PHY.UNT-1:0] tmp_wdt [] = new[4]('{default: 'x});
      logic [PHY.UNT-1:0] tmp_rdt [] = new[4];
      transaction(1'b0, adr, tmp_wdt, tmp_rdt, sts);
      rdt = type(rdt)'({<<PHY.UNT{tmp_rdt[0:4-1]}});  // crop and reverse byte order
    endtask: read32

    task check32 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [4-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic  [4-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                       tmp_sts;
      read32(adr, tmp_rdt, tmp_sts);
      assert (tmp_rdt == rdt) else $error("(rdt=32'h%8x) !== (dat=32'h%8x) mismatch.", tmp_rdt, rdt);
      assert (tmp_sts == sts) else $error("(sts= 1'b%1b) !== (sts= 1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check32

    task write64 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [8-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [PHY.UNT-1:0] tmp_wdt [] = new[8]('{default: 'x});
      logic [PHY.UNT-1:0] tmp_rdt [] = new[8];
      tmp_wdt = {<<PHY.UNT{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(1'b1, adr, tmp_wdt, tmp_rdt, sts);
    endtask: write64

    task read64 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [8-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [PHY.UNT-1:0] tmp_wdt [] = new[8]('{default: 'x});
      logic [PHY.UNT-1:0] tmp_rdt [] = new[8];
      transaction(1'b0, adr, tmp_wdt, tmp_rdt, sts);
      rdt = type(rdt)'({<<PHY.UNT{tmp_rdt[0:8-1]}});  // crop and reverse byte order
    endtask: read64

    task check64 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [8-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic  [8-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                       tmp_sts;
      read64(adr, tmp_rdt, tmp_sts);
      assert (tmp_rdt == rdt) else $error("(rdt=64'h%16x) !== (dat=64'h%16x) mismatch.", tmp_rdt, rdt);
      assert (tmp_sts == sts) else $error("(sts= 1'b%1b) !== (sts= 1'b%1b) mismatch."  , tmp_sts, sts);
    endtask: check64

    task write128 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic [16-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
    logic [PHY.UNT-1:0] tmp_wdt [] = new[16]('{default: 'x});
    logic [PHY.UNT-1:0] tmp_rdt [] = new[16];
    tmp_wdt = {<<PHY.UNT{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
    transaction(1'b1, adr, tmp_wdt, tmp_rdt, sts);
  endtask: write128
 
    task read128 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic [16-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [PHY.UNT-1:0] tmp_wdt [] = new[16]('{default: 'x});
      logic [PHY.UNT-1:0] tmp_rdt [] = new[16];
      transaction(1'b0, adr, tmp_wdt, tmp_rdt, sts);
      rdt = type(rdt)'({<<PHY.UNT{tmp_rdt[0:16-1]}});  // crop and reverse byte order
    endtask: read128
 
    task check128 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic [16-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [16-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                       tmp_sts;
      read128(adr, tmp_rdt, tmp_sts);
      assert (tmp_rdt == rdt) else $error("(rdt=128'h%32x) !== (dat=128'h%32x) mismatch.", tmp_rdt, rdt);
      assert (tmp_sts == sts) else $error("(sts=  1'b%1b) !== (sts=  1'b%1b) mismatch."  , tmp_sts, sts);
    endtask: check128

  endclass: tcb_vip_c

endpackage: tcb_vip_blocking_api_pkg
