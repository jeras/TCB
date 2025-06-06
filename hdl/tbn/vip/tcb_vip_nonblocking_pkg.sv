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
    // configuration parameters
    parameter  type cfg_t = tcb_cfg_t,   // configuration parameter type
    parameter  cfg_t CFG = TCB_CFG_DEF,  // configuration parameter
    // request/response structure types
    parameter  type req_t = tcb_req_t,   // request
    parameter  type rsp_t = tcb_rsp_t,   // response
    // VIP (not to be used in RTL)
    parameter  type vip_t = tcb_vip_t,   // VIP parameter type
    parameter  vip_t VIP = TCB_VIP_DEF,  // VIP parameter
    // debugging options
    parameter  bit  DEBUG = 1'b0,
    // VIP data types
    parameter  type adr_t = int unsigned  // integer data types (byte/shortint/int/longint)
  ) extends tcb_vip_transaction_c #(
    .cfg_t (cfg_t),
    .CFG   (CFG),
    .req_t (req_t),
    .rsp_t (rsp_t),
    .vip_t (vip_t),
    .VIP   (VIP),
    .DEBUG (DEBUG)
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
  // 8-bit write/read transaction put/set tasks
  //////////////////////////////////////////////////////////////////////////////

    task put_write8 (
      ref    transfer_queue_t     que,
      input  adr_t                adr,
      input  logic                ndn,
      input  logic [1-1:0][8-1:0] wdt,
      input  tcb_rsp_sts_t        sts = 'x,
      input  string               id = ""
    );
      logic [8-1:0] dat [] = new[1]('{default: 'x});
      logic [8-1:0] nul [];
      transaction_t tsc;
      int unsigned len;
      dat = {<<8{type(dat)'(wdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: dat, default: 'x}, rsp: '{rdt: nul, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_write8

    task get_write8 (
      ref    transfer_queue_t     que,
      output tcb_rsp_sts_t        sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      sts = tsc.rsp.sts;
    endtask: get_write8

    task put_read8 (
      ref    transfer_queue_t     que,
      input  adr_t                adr,
      input  logic                ndn,
      input  logic [1-1:0][8-1:0] rdt = 'x,
      input  tcb_rsp_sts_t        sts = 'x,
      input  string               id = ""
    );
      logic [8-1:0] dat [] = new[1]('{default: 'x});
      logic [8-1:0] nul [];
      transaction_t tsc;
      int unsigned len;
      dat = {<<8{type(dat)'(rdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: nul, default: 'x}, rsp: '{rdt: dat, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_read8

    task get_read8 (
      ref    transfer_queue_t     que,
      output logic [1-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t        sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      rdt = type(rdt)'({<<8{tsc.rsp.rdt[0:1-1]}});  // crop and reverse byte order
      sts =                 tsc.rsp.sts          ;
    endtask: get_read8

  //////////////////////////////////////////////////////////////////////////////
  // 16-bit write/read transaction put/set tasks
  //////////////////////////////////////////////////////////////////////////////

    task put_write16 (
      ref    transfer_queue_t     que,
      input  adr_t                adr,
      input  logic                ndn,
      input  logic [2-1:0][8-1:0] wdt,
      input  tcb_rsp_sts_t        sts = 'x,
      input  string               id = ""
    );
      logic [8-1:0] dat [] = new[2]('{default: 'x});
      logic [8-1:0] nul [];
      transaction_t tsc;
      int unsigned len;
      dat = {<<8{type(dat)'(wdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: dat, default: 'x}, rsp: '{rdt: nul, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_write16

    task get_write16 (
      ref    transfer_queue_t     que,
      output tcb_rsp_sts_t        sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      sts = tsc.rsp.sts;
    endtask: get_write16

    task put_read16 (
      ref    transfer_queue_t     que,
      input  adr_t                adr,
      input  logic                ndn,
      input  logic [2-1:0][8-1:0] rdt = 'x,
      input  tcb_rsp_sts_t        sts = 'x,
      input  string               id = ""
    );
      logic [8-1:0] dat [] = new[2]('{default: 'x});
      logic [8-1:0] nul [];
      transaction_t tsc;
      int unsigned len;
      dat = {<<8{type(dat)'(rdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: nul, default: 'x}, rsp: '{rdt: dat, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_read16

    task get_read16 (
      ref    transfer_queue_t     que,
      output logic [2-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t        sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      rdt = type(rdt)'({<<8{tsc.rsp.rdt[0:2-1]}});  // crop and reverse byte order
      sts =                 tsc.rsp.sts          ;
    endtask: get_read16

  //////////////////////////////////////////////////////////////////////////////
  // 32-bit write/read transaction put/set tasks
  //////////////////////////////////////////////////////////////////////////////

    task put_write32 (
      ref    transfer_queue_t     que,
      input  adr_t                adr,
      input  logic                ndn,
      input  logic [4-1:0][8-1:0] wdt,
      input  tcb_rsp_sts_t        sts = 'x,
      input  string               id = ""
    );
      logic [8-1:0] dat [] = new[4]('{default: 'x});
      logic [8-1:0] nul [];
      transaction_t tsc;
      int unsigned len;
      dat = {<<8{type(dat)'(wdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: dat, default: 'x}, rsp: '{rdt: nul, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_write32

    task get_write32 (
      ref    transfer_queue_t     que,
      output tcb_rsp_sts_t        sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      sts = tsc.rsp.sts;
    endtask: get_write32

    task put_read32 (
      ref    transfer_queue_t     que,
      input  adr_t                adr,
      input  logic                ndn,
      input  logic [4-1:0][8-1:0] rdt = 'x,
      input  tcb_rsp_sts_t        sts = 'x,
      input  string               id = ""
    );
      logic [8-1:0] dat [] = new[4]('{default: 'x});
      logic [8-1:0] nul [];
      transaction_t tsc;
      int unsigned len;
      dat = {<<8{type(dat)'(rdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: nul, default: 'x}, rsp: '{rdt: dat, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_read32

    task get_read32 (
      ref    transfer_queue_t     que,
      output logic [4-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t        sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      rdt = type(rdt)'({<<8{tsc.rsp.rdt[0:4-1]}});  // crop and reverse byte order
      sts =                 tsc.rsp.sts          ;
    endtask: get_read32

  //////////////////////////////////////////////////////////////////////////////
  // 64-bit write/read transaction put/set tasks
  //////////////////////////////////////////////////////////////////////////////

    task put_write64 (
      ref    transfer_queue_t     que,
      input  adr_t                adr,
      input  logic                ndn,
      input  logic [8-1:0][8-1:0] wdt,
      input  tcb_rsp_sts_t        sts = 'x,
      input  string               id = ""
    );
      logic [8-1:0] dat [] = new[8]('{default: 'x});
      logic [8-1:0] nul [];
      transaction_t tsc;
      int unsigned len;
      dat = {<<8{type(dat)'(wdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: dat, default: 'x}, rsp: '{rdt: nul, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_write64

    task get_write64 (
      ref    transfer_queue_t     que,
      output tcb_rsp_sts_t        sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      sts = tsc.rsp.sts;
    endtask: get_write64

    task put_read64 (
      ref    transfer_queue_t     que,
      input  adr_t                adr,
      input  logic                ndn,
      input  logic [8-1:0][8-1:0] rdt = 'x,
      input  tcb_rsp_sts_t        sts = 'x,
      input  string               id = ""
    );
      logic [8-1:0] dat [] = new[8]('{default: 'x});
      logic [8-1:0] nul [];
      transaction_t tsc;
      int unsigned len;
      dat = {<<8{type(dat)'(rdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: nul, default: 'x}, rsp: '{rdt: dat, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_read64

    task get_read64 (
      ref    transfer_queue_t     que,
      output logic [8-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t        sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      rdt = type(rdt)'({<<8{tsc.rsp.rdt[0:8-1]}});  // crop and reverse byte order
      sts =                 tsc.rsp.sts          ;
    endtask: get_read64

  //////////////////////////////////////////////////////////////////////////////
  // 128-bit write/read transaction put/set tasks
  //////////////////////////////////////////////////////////////////////////////

    task put_write128 (
      ref    transfer_queue_t      que,
      input  adr_t                 adr,
      input  logic                 ndn,
      input  logic [16-1:0][8-1:0] wdt,
      input  tcb_rsp_sts_t         sts = 'x,
      input  string                id = ""
    );
      logic [8-1:0] dat [] = new[16]('{default: 'x});
      logic [8-1:0] nul [];
      transaction_t tsc;
      int unsigned len;
      dat = {<<8{type(dat)'(wdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: dat, default: 'x}, rsp: '{rdt: nul, sts: sts}};
//      $display("DEBUG: tsc=%p", tsc);
      len = put_transaction(que, tsc, id);
//      foreach(que[i])
//      $display("DEBUG: que[%0d] = %p", i, que[i]);
    endtask: put_write128

    task get_write128 (
      ref    transfer_queue_t      que,
      output tcb_rsp_sts_t         sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      sts = tsc.rsp.sts;
    endtask: get_write128

    task put_read128 (
      ref    transfer_queue_t      que,
      input  adr_t                 adr,
      input  logic                 ndn,
      input  logic [16-1:0][8-1:0] rdt = 'x,
      input  tcb_rsp_sts_t         sts = 'x,
      input  string                id = ""
    );
      logic [8-1:0] dat [] = new[16]('{default: 'x});
      logic [8-1:0] nul [];
      transaction_t tsc;
      int unsigned len;
      dat = {<<8{type(dat)'(rdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: nul, default: 'x}, rsp: '{rdt: dat, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_read128

    task get_read128 (
      ref    transfer_queue_t      que,
      output logic [16-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t         sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      rdt = type(rdt)'({<<8{tsc.rsp.rdt[0:16-1]}});  // crop and reverse byte order
      sts =                 tsc.rsp.sts           ;
    endtask: get_read128

  //////////////////////////////////////////////////////////////////////////////
  // 32-bit atomic transaction put/set tasks
  //////////////////////////////////////////////////////////////////////////////

    task put_amo32 (
      ref    transfer_queue_t     que,
      input  tcb_amo_t            amo,
      input  adr_t                adr,
      input  logic                ndn,
      input  logic [4-1:0][8-1:0] wdt,
      input  logic [4-1:0][8-1:0] rdt = 'x,
      input  tcb_rsp_sts_t        sts = 'x,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[4]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[4]('{default: 'x});
      transaction_t tsc;
      int unsigned len;
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      tmp_rdt = {<<8{type(tmp_rdt)'(wdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: tmp_wdt, amo: amo, default: 'x}, rsp: '{rdt: tmp_rdt, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_amo32

    task get_amo32 (
      ref    transfer_queue_t     que,
      output logic [4-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t        sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      rdt = type(rdt)'({<<8{tsc.rsp.rdt[0:4-1]}});  // crop and reverse byte order
      sts =                 tsc.rsp.sts          ;
    endtask: get_amo32

  //////////////////////////////////////////////////////////////////////////////
  // 64-bit atomic transaction put/set tasks
  //////////////////////////////////////////////////////////////////////////////

    task put_amo64 (
      ref    transfer_queue_t     que,
      input  tcb_amo_t            amo,
      input  adr_t                adr,
      input  logic                ndn,
      input  logic [8-1:0][8-1:0] wdt,
      input  logic [8-1:0][8-1:0] rdt = 'x,
      input  tcb_rsp_sts_t        sts = 'x,
      input  string               id = ""
    );
      logic [8-1:0] tmp_wdt [] = new[8]('{default: 'x});
      logic [8-1:0] tmp_rdt [] = new[8]('{default: 'x});
      transaction_t tsc;
      int unsigned len;
      tmp_wdt = {<<8{type(tmp_wdt)'(wdt)}};  // reversed unit/byte order
      tmp_rdt = {<<8{type(tmp_rdt)'(wdt)}};  // reversed unit/byte order
      tsc = '{req: '{ndn: ndn, adr: adr, wdt: tmp_wdt, amo: amo, default: 'x}, rsp: '{rdt: tmp_rdt, sts: sts}};
      len = put_transaction(que, tsc, id);
    endtask: put_amo64

    task get_amo64 (
      ref    transfer_queue_t     que,
      output logic [8-1:0][8-1:0] rdt,
      output tcb_rsp_sts_t        sts
    );
      transaction_t tsc;
      int unsigned len;
      len = get_transaction(que, tsc);
      rdt = type(rdt)'({<<8{tsc.rsp.rdt[0:8-1]}});  // crop and reverse byte order
      sts =                 tsc.rsp.sts          ;
    endtask: get_amo64

  endclass: tcb_vip_nonblocking_c

endpackage: tcb_vip_nonblocking_pkg
