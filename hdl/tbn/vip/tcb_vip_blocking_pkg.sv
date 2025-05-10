////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) blocking API package
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

package tcb_vip_blocking_pkg;

  import tcb_pkg::*;
  import tcb_vip_transfer_pkg::*;
  export tcb_vip_transfer_pkg::*;
  import tcb_vip_transaction_pkg::*;
  export tcb_vip_transaction_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// TCB class
////////////////////////////////////////////////////////////////////////////////

  class tcb_vip_blocking_c #(
    // handshake parameter
    parameter  int unsigned HSK_DLY = TCB_HSK_DEF,  // response delay
    // bus parameters (combined into a structure)
    parameter  type bus_t = tcb_bus_t,  // bus parameter type
    parameter  bus_t BUS = TCB_BUS_DEF,
    // packing parameters
    parameter  type pck_t = tcb_pck_t,  // packing parameter type
    parameter  pck_t PCK = TCB_PCK_DEF,
    // request/response structure types
    parameter  type req_t = tcb_req_t,  // request
    parameter  type rsp_t = tcb_rsp_t,  // response
    // VIP data types
    parameter  type adr_t = int unsigned,  // integer data types (byte/shortint/int/longint)
    // VIP (not to be used in RTL)
    parameter  bit  VIP = 0, // VIP end node
    // debugging options
    parameter  bit  DEBUG = 1'b0
  ) extends tcb_vip_transaction_c #(
    .HSK_DLY (HSK_DLY),
    .bus_t   (bus_t),
    .BUS     (BUS),
    .pck_t   (pck_t),
    .PCK     (PCK),
    .req_t   (req_t),
    .rsp_t   (rsp_t),
    .VIP     (VIP),
    .DEBUG   (DEBUG)
  );

    //constructor
    function new(
      input tcb_vif_t tcb,
      input string DIR = "MON"
    );
      super.new(
        .tcb (tcb),
        .DIR (DIR)
      );
    endfunction: new

  //////////////////////////////////////////////////////////////////////////////
  // local state
  //////////////////////////////////////////////////////////////////////////////

    static tcb_endian_t ndn = TCB_LITTLE;

  //////////////////////////////////////////////////////////////////////////////
  // transaction sequence blocking API
  //////////////////////////////////////////////////////////////////////////////

    task automatic transaction (
      // request
      input  logic         wen,
      input  adr_t         adr,
      ref    logic [8-1:0] wdt [],
      // response
      ref    logic [8-1:0] rdt [],
      output tcb_rsp_sts_t sts,
      // identification
      input  string        id = ""
    );
      int unsigned len;
      transfer_array_t transfer_array;
      transaction_t transaction;
      // request
      transaction = '{req: '{ndn: ndn, wen: wen, adr: adr, wdt: wdt}, rsp: '{rdt: rdt, sts: sts}};
      len = set_transaction(transaction, transfer_array, id);
      // transaction
//      $display("DEBUG: swq-: transfer_array = %p", transfer_array);
      transfer_sequencer(transfer_array);
//      $display("DEBUG: swq+: transfer_array = %p", transfer_array);
      // response
      len = get_transaction(transaction, transfer_array);
      // cleanup
      transfer_array.delete();
      // outputs
      rdt = transaction.rsp.rdt;
      sts = transaction.rsp.sts;
    endtask: transaction

  //////////////////////////////////////////////////////////////////////////////
  // write/read/check
  //////////////////////////////////////////////////////////////////////////////

    task write8 (
      input  adr_t                adr,
      input  logic [1-1:0][8-1:0] wdt,
      output tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[1]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[1];
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(1'b1, adr, tmp_wdt, tmp_rdt, sts, id);
    endtask: write8

    task read8 (
      input  adr_t                adr,
      output logic [1-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[1]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[1];
      transaction(1'b0, adr, tmp_wdt, tmp_rdt, sts, id);
      rdt = type(rdt)'({<<8{tmp_rdt[0:1-1]}});  // crop and reverse byte order
    endtask: read8

    task check8 (
      input  adr_t                adr,
      input  logic [1-1:0][8-1:0] rdt,
      input  tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic  [1-1:0][8-1:0] tmp_rdt;
      tcb_rsp_sts_t         tmp_sts;
      read8(adr, tmp_rdt, tmp_sts, id);
      assert (tmp_rdt == rdt) else $error("(rdt=8'h%2x) !== (dat=8'h%2x) mismatch.", tmp_rdt, rdt);
      assert (tmp_sts == sts) else $error("(sts=1'b%1b) !== (sts=1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check8

    task write16 (
      input  adr_t                adr,
      input  logic [2-1:0][8-1:0] wdt,
      output tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[2]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[2];
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(1'b1, adr, tmp_wdt, tmp_rdt, sts, id);
    endtask: write16

    task read16 (
      input  adr_t                adr,
      output logic [2-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[2]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[2];
      transaction(1'b0, adr, tmp_wdt, tmp_rdt, sts, id);
      rdt = type(rdt)'({<<8{tmp_rdt[0:2-1]}});  // crop and reverse byte order
    endtask: read16

    task check16 (
      input  adr_t                adr,
      input  logic [2-1:0][8-1:0] rdt,
      input  tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic  [2-1:0][8-1:0] tmp_rdt;
      tcb_rsp_sts_t         tmp_sts;
      read16(adr, tmp_rdt, tmp_sts, id);
      assert (tmp_rdt == rdt) else $error("(rdt=16'h%4x) !== (dat=16'h%4x) mismatch.", tmp_rdt, rdt);
      assert (tmp_sts == sts) else $error("(sts= 1'b%1b) !== (sts= 1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check16

    task write32 (
      input  adr_t                adr,
      input  logic [4-1:0][8-1:0] wdt,
      output tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[4]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[4];
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(1'b1, adr, tmp_wdt, tmp_rdt, sts, id);
    endtask: write32

    task read32 (
      input  adr_t                adr,
      output logic [4-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[4]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[4];
      transaction(1'b0, adr, tmp_wdt, tmp_rdt, sts, id);
      rdt = type(rdt)'({<<8{tmp_rdt[0:4-1]}});  // crop and reverse byte order
    endtask: read32

    task check32 (
      input  adr_t                adr,
      input  logic [4-1:0][8-1:0] rdt,
      input  tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic  [4-1:0][8-1:0] tmp_rdt;
      tcb_rsp_sts_t         tmp_sts;
      read32(adr, tmp_rdt, tmp_sts, id);
      assert (tmp_rdt == rdt) else $error("(rdt=32'h%8x) !== (dat=32'h%8x) mismatch.", tmp_rdt, rdt);
      assert (tmp_sts == sts) else $error("(sts= 1'b%1b) !== (sts= 1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check32

    task write64 (
      input  adr_t                adr,
      input  logic [8-1:0][8-1:0] wdt,
      output tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[8]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[8];
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(1'b1, adr, tmp_wdt, tmp_rdt, sts, id);
    endtask: write64

    task read64 (
      input  adr_t                adr,
      output logic [8-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[8]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[8];
      transaction(1'b0, adr, tmp_wdt, tmp_rdt, sts, id);
      rdt = type(rdt)'({<<8{tmp_rdt[0:8-1]}});  // crop and reverse byte order
    endtask: read64

    task check64 (
      input  adr_t                adr,
      input  logic [8-1:0][8-1:0] rdt,
      input  tcb_rsp_sts_t        sts,
      input  string               id = ""
    );
      logic  [8-1:0][8-1:0] tmp_rdt;
      tcb_rsp_sts_t         tmp_sts;
      read64(adr, tmp_rdt, tmp_sts);
      assert (tmp_rdt == rdt) else $error("(rdt=64'h%16x) !== (dat=64'h%16x) mismatch.", tmp_rdt, rdt);
      assert (tmp_sts == sts) else $error("(sts= 1'b%1b) !== (sts= 1'b%1b) mismatch."  , tmp_sts, sts);
    endtask: check64

    task write128 (
      input  adr_t                 adr,
      input  logic [16-1:0][8-1:0] wdt,
      output tcb_rsp_sts_t         sts,
      input  string                id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[16]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[16];
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(1'b1, adr, tmp_wdt, tmp_rdt, sts, id);
    endtask: write128
 
    task read128 (
      input  adr_t                 adr,
      output logic [16-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t         sts,
      input  string                id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[16]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[16];
      transaction(1'b0, adr, tmp_wdt, tmp_rdt, sts, id);
      rdt = type(rdt)'({<<8{tmp_rdt[0:16-1]}});  // crop and reverse byte order
    endtask: read128
 
    task check128 (
      input  adr_t                 adr,
      input  logic [16-1:0][8-1:0] rdt,
      input  tcb_rsp_sts_t         sts,
      input  string                id = ""
    );
      logic [16-1:0][8-1:0] tmp_rdt;
      tcb_rsp_sts_t         tmp_sts;
      read128(adr, tmp_rdt, tmp_sts, id);
      assert (tmp_rdt == rdt) else $error("(rdt=128'h%32x) !== (dat=128'h%32x) mismatch.", tmp_rdt, rdt);
      assert (tmp_sts == sts) else $error("(sts=  1'b%1b) !== (sts=  1'b%1b) mismatch."  , tmp_sts, sts);
    endtask: check128

  endclass: tcb_vip_blocking_c

endpackage: tcb_vip_blocking_pkg
