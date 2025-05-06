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
// TCB transaction class
////////////////////////////////////////////////////////////////////////////////

  class tcb_vip_transaction_c #(
    // handshake parameter
    parameter  int unsigned HSK_DLY = TCB_HSK_DEF,    // response delay
    // bus parameters (combined into a structure)
    parameter  type bus_t = tcb_bus_t,  // bus parameter type
    parameter  bus_t BUS = TCB_BUS_DEF,
    // packing parameters
    parameter  type pck_t = tcb_pck_t,  // packing parameter type
    parameter  pck_t PCK = TCB_PCK_DEF,
    // request/response structure types
    parameter  type req_t = tcb_req_t,  // request
    parameter  type rsp_t = tcb_rsp_t,  // response
    // VIP (not to be used in RTL)
    parameter  bit  VIP = 0, // VIP end node
    // debugging options
    parameter  bit  DEBUG = 1'b0
  ) extends tcb_vip_transfer_c #(
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

    // constructor
    function new(
      tcb_vif_t tcb,
      string DIR = "MON"
    );
      super.new(
        .tcb (tcb),
        .DIR (DIR)
      );
    endfunction: new

  //////////////////////////////////////////////////////////////////////////////
  // local types, constants, functions
  //////////////////////////////////////////////////////////////////////////////

    // dummy transfer request (only used to calculate local parameters)
    req_t dummy_req;

    // local parameters
    localparam int unsigned BUS_ADR = $bits(dummy_req.adr);
    localparam int unsigned BUS_DAT = $bits(dummy_req.wdt);
    localparam int unsigned BUS_BEN = $bits(dummy_req.ben);
    localparam int unsigned BUS_SIZ = $bits(dummy_req.siz);
    localparam int unsigned BUS_MAX = $clog2(BUS_BEN);

    // TCB transaction request structure
    typedef struct {
      // request
      tcb_endian_t        ndn;
      logic               wen;
      logic [BUS_ADR-1:0] adr;
      logic       [8-1:0] wdt [];
    } transaction_req_t;

    // TCB transaction response structure
    typedef struct {
      // response
      logic [8-1:0] rdt [];
      tcb_rsp_sts_t sts;
    } transaction_rsp_t;

    // TCB transaction structure
    typedef struct {
      transaction_req_t req;
      transaction_rsp_t rsp;
    } transaction_t;

    // logarithmic size to byte enable
    static function automatic logic [BUS_BEN-1:0] siz2ben (
      input [BUS_SIZ-1:0] siz,
      input [BUS_MAX-1:0] off = '0
    );
      siz2ben = '0;
      for (int unsigned i=0; i<BUS_BEN; i++) begin
        siz2ben[(i+off)%BUS_BEN] = (i < 2**siz) ? 1'b1 : 1'b0;
      end
    endfunction: siz2ben

    // byte enable to logarithmic size
    static function automatic logic [BUS_BEN-1:0] ben2siz (
      input [BUS_BEN-1:0] ben,
      input [BUS_MAX-1:0] off = '0
    );
      int unsigned cnt = 0;
      for (int unsigned i=0; i<BUS_BEN; i++) begin
        if (ben[(i+off)%BUS_BEN])  cnt++;
      end
      ben2siz = $clog2(cnt);
    endfunction: ben2siz

  //////////////////////////////////////////////////////////////////////////////
  // set transfer array from transaction
  //////////////////////////////////////////////////////////////////////////////

    // read/write request transaction of power of 2 size
    static function automatic transfer_queue_t set_transaction (
      input transaction_t transaction,
      input string      id = ""
    );
      // the requested transaction is organized into transfer_array
      int unsigned siz;  // transaction side (units/bytes)
      int unsigned len;  // transaction length (transfers)
      // return transfer queue
      transfer_queue_t transfer_queue;

      // data size
      siz = $clog2(transaction.req.wdt.size());
      assert (transaction.req.wdt.size() == 2**siz) else $error("Data array size is not a power of 2.");
      // transaction length (number of transfer items)
      if (2**siz < BUS_BEN)  len = 1;
      else                   len = 2**siz / BUS_BEN;

      // alignment check
      // TODO: implement this later
      ////adr%siz==0
      //if (PCK.ALN > 0) begin
      //  logic [PCK.ALN-1:0] adr_alw;
      //  adr_alw = transaction.req.adr[(PCK.ALN>0?(PCK.ALN-1):0):0];
      //  if (|adr_alw) begin
      //    $error("Transaction address is not aligned to supported size. adr[%0d:0]=%0d'b%b", PCK.ALN-1, PCK.ALN, adr_alw);
      //  end
      //end

      // loop over transfers within transaction
      for (int unsigned i=0; i<len; i++) begin
        transfer_t tmp;
        // request signals
        tmp.req.frm = (i == len-1) ? 1'b0 : 1'b1;
        tmp.req.wen = transaction.req.wen;
        tmp.req.ndn = transaction.req.ndn;
        tmp.req.adr = transaction.req.adr + i*BUS_BEN;
        case (BUS.MOD)
          TCB_MOD_LOG_SIZE:  tmp.req.siz = BUS_MAX;
          TCB_MOD_BYTE_ENA:  tmp.req.ben = '1;
        endcase
        // response
        tmp.rsp.sts = transaction.rsp.sts;
        // ID
        tmp.id = $sformatf("%s[%0d]", id, i);
        // add transfer to queue
        transfer_queue.push_back(tmp);
      end
      if (siz < BUS_MAX) begin
        case (BUS.MOD)
          TCB_MOD_LOG_SIZE:  transfer_queue[0].req.siz = siz;
          TCB_MOD_BYTE_ENA:  transfer_queue[0].req.ben = siz2ben(siz, transaction.req.adr[BUS_MAX-1:0]);  // TODO: this will not work for BUS_MAX = 0
        endcase
      end

//      $display("DEBUG: transaction_request: siz = %d, len = %d", siz, len);
//      $display("DEBUG: transaction_request: transfer_queue = %p", transfer_queue);
      // data signals
      for (int unsigned i=0; i<2**siz; i++) begin
        // temporary variables
        int unsigned cnt;  // transfer counter
        int unsigned byt;  // byte index
        // transfer counter
        cnt = i / BUS_BEN;
        // mode logarithmic size vs. byte enable
        case (BUS.MOD)
          TCB_MOD_LOG_SIZE:  byt = i;  // all data bytes are LSB aligned
          TCB_MOD_BYTE_ENA:  byt = (i + transaction.req.adr) % BUS_BEN;
        endcase
        // order descending/ascending
        case (PCK.ORD)
          TCB_ORD_DESCENDING:  byt = byt;                // no change
          TCB_ORD_ASCENDING :  byt = BUS_BEN - 1 - byt;  // reverse byte order
        endcase
        // request
        transfer_queue[cnt].req.ben[byt] = 1'b1;
        // request endianness
        case (transaction.req.ndn)
          TCB_NDN_LITTLE:  transfer_queue[cnt].req.wdt[byt] = transaction.req.wdt[             i];
          TCB_NDN_BIG   :  transfer_queue[cnt].req.wdt[byt] = transaction.req.wdt[2**siz - 1 - i];
        endcase
        // response endianness
        case (transaction.req.ndn)
          TCB_NDN_LITTLE:  transfer_queue[cnt].rsp.rdt[byt] = transaction.rsp.rdt[             i];
          TCB_NDN_BIG   :  transfer_queue[cnt].rsp.rdt[byt] = transaction.rsp.rdt[2**siz - 1 - i];
        endcase
      end

      //      $display("DEBUG: inside: transfer_queue.size() = %d", transfer_queue.size());
      return(transfer_queue);
    endfunction: set_transaction

  //////////////////////////////////////////////////////////////////////////////
  // get transaction transfer array
  //////////////////////////////////////////////////////////////////////////////

    // read/write response transaction of power of 2 size
    static function automatic transaction_t get_transaction (
      ref transfer_array_t transfer_array
    );
      // transaction response
      int unsigned siz;  // transaction side (units/bytes)
      int unsigned len;  // transaction length (transfers)
      // loop index
      int unsigned i;
      // return transaction response
      transaction_t transaction;

      // transaction length (number of transfer items)
      len = transfer_array.size();
      // data size
      siz = $clog2(len*BUS_BEN);

      // request signals (first transfer)
      transaction.req.wen =              (transfer_array[0].req.wen);
      transaction.req.ndn = tcb_endian_t'(transfer_array[0].req.ndn);
      transaction.req.adr =              (transfer_array[0].req.adr);

      siz = 0;
      i = 0;
      do begin
        // request signals
        assert (transfer_array[i].req.wen == transaction.req.wen            ) else $warning("wen mismatch");
        assert (transfer_array[i].req.ndn == transaction.req.ndn            ) else $warning("ndn mismatch");
        assert (transfer_array[i].req.adr == transaction.req.adr + i*BUS_BEN) else $warning("adr mismatch");
        case (BUS.MOD)
          TCB_MOD_LOG_SIZE:  siz += transfer_array[0].req.siz;
          TCB_MOD_BYTE_ENA:  siz += ben2siz(transfer_array[0].req.ben, transaction.req.adr[BUS_MAX-1:0]);  // TODO: this will not work for BUS_MAX = 0
        endcase
        // response status
        transaction.rsp.sts |= transfer_array[i].rsp.sts;
      end while (transfer_array[i++].req.frm);
      len = i;

      // initialize response
      transaction.rsp.rdt = new[2**siz]('{default: 'x});
      transaction.rsp.sts = '0;

      // data signals
      for (int unsigned i=0; i<2**siz; i++) begin
        // temporary variables
        int unsigned byt;  // byte index
        int unsigned cnt;  // transfer counter
        // transfer counter
        cnt = i / BUS_BEN;
        // mode logarithmic size vs. byte enable
        case (BUS.MOD)
          TCB_MOD_LOG_SIZE:  byt =  i                                % BUS_BEN;  // all data bytes are LSB aligned
          TCB_MOD_BYTE_ENA:  byt = (i + transfer_array[cnt].req.adr) % BUS_BEN;
        endcase
        // order descending/ascending
        case (PCK.ORD)
          TCB_ORD_DESCENDING:  byt = byt;                // no change
          TCB_ORD_ASCENDING :  byt = BUS_BEN - 1 - byt;  // reverse byte order
        endcase
        // request endianness
        case (transfer_array[cnt].req.ndn)
          TCB_NDN_LITTLE:  transaction.req.wdt[          i] = transfer_array[cnt].req.wdt[byt];
          TCB_NDN_BIG   :  transaction.req.wdt[siz - 1 - i] = transfer_array[cnt].req.wdt[byt];
        endcase
        // response  endianness
        case (transfer_array[cnt].req.ndn)
          TCB_NDN_LITTLE:  transaction.rsp.rdt[          i] = transfer_array[cnt].rsp.rdt[byt];
          TCB_NDN_BIG   :  transaction.rsp.rdt[siz - 1 - i] = transfer_array[cnt].rsp.rdt[byt];
        endcase
      end

      //      $display("DEBUG: transaction.rsp.rdt = %p", transaction.rsp.rdt);
      return(transaction);
    endfunction: get_transaction

  endclass: tcb_vip_transaction_c

endpackage: tcb_vip_transaction_pkg
