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

package tcb_vip_transaction_pkg;

  import tcb_pkg::*;
  import tcb_vip_transfer_pkg::*;
  export tcb_vip_transfer_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// TCB class
////////////////////////////////////////////////////////////////////////////////

  class tcb_vip_transaction_c #(
    parameter       tcb_phy_t PHY = TCB_PAR_PHY_DEF,
    parameter  type tcb_req_cmd_t = tcb_req_cmd_def_t,
    parameter  type tcb_rsp_sts_t = tcb_rsp_sts_def_t
  ) extends tcb_vip_transfer_c #(
    .PHY           (PHY),
    .tcb_req_cmd_t (tcb_req_cmd_t),
    .tcb_rsp_sts_t (tcb_rsp_sts_t)
  );

////////////////////////////////////////////////////////////////////////////////
// transaction class
////////////////////////////////////////////////////////////////////////////////

      // TCB transaction request structure
      typedef struct {
        // request
        tcb_cfg_endian_t             ndn;
        logic                        wen;
        logic          [PHY.ADR-1:0] adr;
        logic   [8-1:0][PHY.UNT-1:0] wdt;
      } transaction_request_t;

      // TCB transaction response structure
      typedef struct {
        // response
        logic   [8-1:0][PHY.UNT-1:0] rdt;
        tcb_rsp_sts_t                sts;
      } transaction_response_t;

      // TCB transaction structure
      typedef struct {
        transaction_request_t  req;
        transaction_response_t rsp;
      } transaction_t;

      // read/write request transaction of power of 2 size
      static function automatic transfer_array_t transaction_request (
        int unsigned          siz,
        // TCB transaction structure
        transaction_request_t transaction_req
      );
        // temporary variables
        int unsigned byt;  // byte index
        int unsigned off;  // address offset
        // the requested transaction is organized into transfer_array
        int unsigned len;
        // return transfer array
        transfer_array_t transfer_array;
        // number of transfer_array
        len = siz / PHY_BEN + (siz % PHY_BEN ? 1 : 0);
        transfer_array = new[len];
        transfer_array = new[len]('{default: TRANSFER_INIT});
        // check if the transfer meets size requirements
        if (siz != 2**$clog2(siz)) begin
          $error("ERROR: Transaction size is not power of 2.");
        end
        // check if the transfer meets alignment requirements
//        adr%siz==0
        if (PHY.ALN > 0) begin
          logic [PHY.ALN-1:0] adr_alw;
          adr_alw = transaction_req.adr[(PHY.ALN>0?(PHY.ALN-1):0):0];
          if (|adr_alw) begin
            $error("ERROR: Transaction address is not aligned to supported size. adr[%0d:0]=%0d'b%b", PHY.ALN-1, PHY.ALN, adr_alw);
          end
        end
        // control and address signals
        for (int unsigned i=0; i<len; i++) begin
          // request optional
          transfer_array[i].req.cmd = '{lck: (i == len-1) ? 1'b0 : 1'b1, default: '0};
          transfer_array[i].req.wen = transaction_req.wen;
          transfer_array[i].req.ndn = transaction_req.ndn;
          transfer_array[i].req.adr = transaction_req.adr;
          transfer_array[i].req.ben = '0;
          transfer_array[i].req.siz = $clog2(PHY_BEN);
        end
        if (siz <= PHY_BEN) begin
          transfer_array[0].req.siz = $clog2(    siz);
        end
        // data signals
        for (int unsigned i=0; i<siz; i++) begin
          // address offset
          off = i / PHY_BEN;
          // mode processor/memory
          if (PHY.MOD == TCB_LOG_SIZE) begin
            // all data bytes are LSB aligned
            byt = i;
          end else if (PHY.MOD == TCB_BYTE_ENA) begin
            // all data bytes are LSB aligned
            byt = (i + transaction_req.adr) % PHY_BEN;
          end
          // order descending/ascending
          if (PHY.ORD == TCB_ASCENDING) begin
            byt = PHY_BEN - 1 - byt;
          end
          // request
          transfer_array[off].req.ben[byt] = 1'b1;
          // endianness
          if (transaction_req.ndn == TCB_LITTLE) begin
            transfer_array[off].req.wdt[byt] = transaction_req.wdt[          i];
          end else begin
            transfer_array[off].req.wdt[byt] = transaction_req.wdt[siz - 1 - i];
          end
        end
        return(transfer_array);
      endfunction: transaction_request

      // read/write response transaction of power of 2 size
      static function automatic transaction_response_t transaction_response (
        int unsigned          siz,
        transfer_array_t transfer_array
      );
        // temporary variables
        int unsigned byt;  // byte index
        int unsigned off;  // address offset
        // transaction response
        int unsigned len;
        transaction_response_t transaction_rsp = '{rdt: 'x, sts: '0};
        // data signals
        for (int unsigned i=0; i<siz; i++) begin
          // address offset
          off = i / PHY_BEN;
          // mode processor/memory
          if (PHY.MOD == TCB_LOG_SIZE) begin
            // all data bytes are LSB aligned
            byt = i;
          end else if (PHY.MOD == TCB_BYTE_ENA) begin
            // all data bytes are LSB aligned
            byt = (i + transfer_array[off].req.adr) % PHY_BEN;
          end
          // order descending/ascending
          if (PHY.ORD == TCB_ASCENDING) begin
            byt = PHY_BEN - 1 - byt;
          end
          // endianness
          if (transfer_array[off].req.ndn == TCB_LITTLE) begin
            transaction_rsp.rdt[          i] = transfer_array[off].rsp.rdt[byt];
          end else begin
            transaction_rsp.rdt[siz - 1 - i] = transfer_array[off].rsp.rdt[byt];
          end
          // response status
          transaction_rsp.sts               |= transfer_array[off].rsp.sts;
        end
        return(transaction_rsp);
      endfunction: transaction_response

////////////////////////////////////////////////////////////////////////////////
// transaction
////////////////////////////////////////////////////////////////////////////////

    task automatic transaction8 (
      // request
      input  logic                            wen,
      input  logic              [PHY.ADR-1:0] adr,
      input  logic       [1-1:0][PHY.UNT-1:0] wdt,
      // response
      output logic       [1-1:0][PHY.UNT-1:0] rdt,
      output tcb_rsp_sts_t                    sts,
      // endianness
      input  tcb_cfg_endian_t                 ndn = TCB_LITTLE
    );
      transfer_array_t transfer_array;
      transaction_t transaction;
      // request
      transaction.req = '{ndn: ndn, wen: wen, adr: adr, wdt: wdt};
      transfer_array = transaction_request(1, transaction.req);
      // transaction
      transfer_sequencer(transfer_array);
      // response
      transaction.rsp = transaction_response(1, transfer_array);
      // cleanup
      transfer_array.delete;
      // outputs
      rdt = transaction.rsp.rdt;
      sts = transaction.rsp.sts;
    endtask: transaction8

    task automatic transaction16 (
      // request
      input  logic                            wen,
      input  logic              [PHY.ADR-1:0] adr,
      input  logic       [2-1:0][PHY.UNT-1:0] wdt,
      // response
      output logic       [2-1:0][PHY.UNT-1:0] rdt,
      output tcb_rsp_sts_t                    sts,
      // endianness
      input  tcb_cfg_endian_t                 ndn = TCB_LITTLE
    );
      transfer_array_t transfer_array;
      transaction_t transaction;
      // request
      transaction.req = '{ndn: ndn, wen: wen, adr: adr, wdt: wdt};
      transfer_array = transaction_request(2, transaction.req);
      // transaction
      transfer_sequencer(transfer_array);
      // response
      transaction.rsp = transaction_response(2, transfer_array);
      // cleanup
      transfer_array.delete;
      // outputs
      rdt = transaction.rsp.rdt;
      sts = transaction.rsp.sts;
    endtask: transaction16

    task automatic transaction32 (
      // request
      input  logic                            wen,
      input  logic              [PHY.ADR-1:0] adr,
      input  logic       [4-1:0][PHY.UNT-1:0] wdt,
      // response
      output logic       [4-1:0][PHY.UNT-1:0] rdt,
      output tcb_rsp_sts_t                    sts,
      // endianness
      input  tcb_cfg_endian_t                 ndn = TCB_LITTLE
    );
      transfer_array_t transfer_array;
      transaction_t transaction;
      // request
      transaction.req = '{ndn: ndn, wen: wen, adr: adr, wdt: wdt};
      transfer_array = transaction_request(4, transaction.req);
      // transaction
      transfer_sequencer(transfer_array);
      // response
      transaction.rsp = transaction_response(4, transfer_array);
      // cleanup
      transfer_array.delete;
      // outputs
      rdt = transaction.rsp.rdt;
      sts = transaction.rsp.sts;
    endtask: transaction32

    task automatic transaction64 (
      // request
      input  logic                            wen,
      input  logic              [PHY.ADR-1:0] adr,
      input  logic       [8-1:0][PHY.UNT-1:0] wdt,
      // response
      output logic       [8-1:0][PHY.UNT-1:0] rdt,
      output tcb_rsp_sts_t                    sts,
      // endianness
      input  tcb_cfg_endian_t                 ndn = TCB_LITTLE
    );
      transfer_array_t transfer_array;
      transaction_t transaction;
      // request
      transaction.req = '{ndn: ndn, wen: wen, adr: adr, wdt: wdt};
      transfer_array = transaction_request(8, transaction.req);
      // transaction
      transfer_sequencer(transfer_array);
      // response
      transaction.rsp = transaction_response(8, transfer_array);
      // cleanup
      transfer_array.delete;
      // outputs
      rdt = transaction.rsp.rdt;
      sts = transaction.rsp.sts;
    endtask: transaction64

    task automatic transaction128 (
      // request
      input  logic                            wen,
      input  logic              [PHY.ADR-1:0] adr,
      input  logic      [16-1:0][PHY.UNT-1:0] wdt,
      // response
      output logic      [16-1:0][PHY.UNT-1:0] rdt,
      output tcb_rsp_sts_t                    sts,
      // endianness
      input  tcb_cfg_endian_t                 ndn = TCB_LITTLE
    );
      transfer_array_t transfer_array;
      transaction_t transaction;
      // request
      transaction.req = '{ndn: ndn, wen: wen, adr: adr, wdt: wdt};
      transfer_array = transaction_request(16, transaction.req);
      // transaction
      transfer_sequencer(transfer_array);
      // response
      transaction.rsp = transaction_response(16, transfer_array);
      // cleanup
      transfer_array.delete;
      // outputs
      rdt = transaction.rsp.rdt;
      sts = transaction.rsp.sts;
    endtask: transaction128

  endclass: tcb_vip_transaction_c

endpackage: tcb_vip_transaction_pkg
