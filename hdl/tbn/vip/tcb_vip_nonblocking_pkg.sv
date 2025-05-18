////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) non-blocking API package
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

package tcb_vip_nonblocking_pkg;

  import tcb_pkg::*;
  import tcb_vip_transfer_pkg::*;
  export tcb_vip_transfer_pkg::*;
  import tcb_vip_transaction_pkg::*;
  export tcb_vip_transaction_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// TCB class
////////////////////////////////////////////////////////////////////////////////

  class tcb_vip_nonblocking_c #(
    // handshake parameters
    parameter  type hsk_t = tcb_hsk_t,   // handshake parameter type
    parameter  hsk_t HSK = TCB_HSK_DEF,  // handshake parameter
    // bus parameters
    parameter  type bus_t = tcb_bus_t,   // bus parameter type
    parameter  bus_t BUS = TCB_BUS_DEF,  // bus parameter
    // packing parameters
    parameter  type pck_t = tcb_pck_t,   // packing parameter type
    parameter  pck_t PCK = TCB_PCK_DEF,  // packing parameter
    // request/response structure types
    parameter  type req_t = tcb_req_t,  // request
    parameter  type rsp_t = tcb_rsp_t,  // response
    // VIP (not to be used in RTL)
    parameter  bit  VIP = 0, // VIP end node
    // debugging options
    parameter  bit  DEBUG = 1'b0,
    // VIP data types
    parameter  type adr_t = int unsigned  // integer data types (byte/shortint/int/longint)
  ) extends tcb_vip_transaction_c #(
    .hsk_t   (hsk_t),
    .HSK     (HSK),
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
  // write/read/check
  //////////////////////////////////////////////////////////////////////////////

/*
    task access8 (
      input  logic                wen,
      input  adr_t                adr,
      input  logic [1-1:0][8-1:0] wdt,
      output logic [1-1:0][8-1:0] rdt,
      output logic                sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[1];
      logic [8-1:0] tmp_rdt [] = new[1];
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(wen, adr, tmp_wdt, tmp_rdt, sts, id);
      rdt = type(rdt)'({<<8{tmp_rdt[0:1-1]}});  // crop and reverse byte order
    endtask: access8

    task access16 (
      input  logic                wen,
      input  adr_t                adr,
      input  logic [2-1:0][8-1:0] wdt,
      output logic [2-1:0][8-1:0] rdt,
      output logic                sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[2]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[2];
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(wen, adr, tmp_wdt, tmp_rdt, sts, id);
      rdt = type(rdt)'({<<8{tmp_rdt[0:2-1]}});  // crop and reverse byte order
    endtask: access16

    task write32 (
      input  logic                wen,
      input  adr_t                adr,
      input  logic [4-1:0][8-1:0] wdt,
      output logic [4-1:0][8-1:0] rdt,
      output logic                sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[4]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[4];
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(wen, adr, tmp_wdt, tmp_rdt, sts, id);
      rdt = type(rdt)'({<<8{tmp_rdt[0:4-1]}});  // crop and reverse byte order
    endtask: write32

    task write64 (
      input  logic                wen,
      input  adr_t                adr,
      input  logic [8-1:0][8-1:0] wdt,
      output logic [8-1:0][8-1:0] rdt,
      output logic                sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[8]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[8];
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(wen, adr, tmp_wdt, tmp_rdt, sts, id);
      rdt = type(rdt)'({<<8{tmp_rdt[0:8-1]}});  // crop and reverse byte order
    endtask: write64

    task write128 (
      input  logic                 wen,
      input  adr_t                 adr,
      input  logic [16-1:0][8-1:0] wdt,
      output logic [16-1:0][8-1:0] rdt,
      output logic                 sts,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[16]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[16];
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      transaction(wen, adr, tmp_wdt, tmp_rdt, sts, id);
      rdt = type(rdt)'({<<8{tmp_rdt[0:16-1]}});  // crop and reverse byte order
    endtask: write128

*/
  endclass: tcb_vip_nonblocking_c

endpackage: tcb_vip_nonblocking_pkg
