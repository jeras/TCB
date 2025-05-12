////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) transaction package
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
    localparam int unsigned BUS_ADR = BUS.ADR;  // TODO: this is only needed by VCS
    localparam int unsigned BUS_BEN = BUS.DAT/8;
    localparam int unsigned BUS_MAX = $clog2(BUS_BEN);
    localparam int unsigned BUS_SIZ = $clog2(BUS_MAX+1);

    // TCB transaction request structure
    typedef struct {
      // request
      logic               ndn;
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
    static function automatic int unsigned set_transaction (
      ref   transfer_queue_t transfer_queue,
      input transaction_t    transaction,
      input string           id = ""
    );
      // write/read data linear size
      int unsigned wdt_size;
      int unsigned rdt_size;
      int unsigned     size;
      // request/response logarithmic siz
      int unsigned wdt_siz;
      int unsigned rdt_siz;

      int unsigned len;  // transaction length (transfers)

      // transfer counter
      int unsigned cnt = 0;
      transfer_t tmp;

      // return transfer queue

      // write/read data linear size
      wdt_size = transaction.req.wdt.size();
      rdt_size = transaction.rsp.rdt.size();
      // request/response logarithmic siz
      wdt_siz = $clog2(wdt_size);
      rdt_siz = $clog2(rdt_size);

      // write access
      if ( (BUS.CHN == TCB_CHN_WRITE_ONLY) || ((BUS.CHN == TCB_CHN_HALF_DUPLEX) && (transaction.req.wen == 1'b1)) ) begin
        size = wdt_size;
        assert (wdt_size == 2**wdt_siz) else $error("Write data array size is not a power of 2.");
      end
      // read access
      if ( (BUS.CHN == TCB_CHN_READ_ONLY) || ((BUS.CHN == TCB_CHN_HALF_DUPLEX) && (transaction.req.wen == 1'b0)) ) begin
        size = rdt_size;
        assert (rdt_size == 2**rdt_siz) else $error("Read data array size is not a power of 2.");
      end
      // full duplex access
      if (BUS.CHN == TCB_CHN_FULL_DUPLEX) begin
        // check if write/read data arrays are of the same size
        if (transaction.req.wen === 1'bx) begin
          assert (wdt_size == rdt_size) else $error("Write/read data arrays are not of the same size.");
        end
        // write access
        if (transaction.req.wen === 1'b1) begin
          size = rdt_size;
          assert (wdt_size == 2**wdt_siz) else $error("Write data array size is not a power of 2.");
        end
        // read access
        if (transaction.req.wen === 1'b0) begin
          size = rdt_size;
          assert (rdt_size == 2**rdt_siz) else $error("Read data array size is not a power of 2.");
        end
      end

      // transaction length (number of transfer items)
      if (size < BUS_BEN)  len = 1;
      else                 len = size / BUS_BEN;

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

//      $display("DEBUG: transaction_request: siz = %d, len = %d", siz, len);
//      $display("DEBUG: transaction_request: transfer_queue = %p", transfer_queue);

      // data signals
      for (int unsigned i=0; i<size; i++) begin
        // temporary variables
        int unsigned byt;  // transfer byte index
        int unsigned idx;  // transaction byte index
        // mode logarithmic size vs. byte enable
        case (BUS.MOD)
          TCB_MOD_LOG_SIZE:  byt =  i                                     % BUS_BEN;  // all data bytes are LSB aligned
          TCB_MOD_BYTE_ENA:  byt = (i + transaction.req.adr[BUS_MAX-1:0]) % BUS_BEN;
        endcase
        // endianness
        if (transaction.req.ndn ^ BUS.ORD)  idx =        i    ;
        else                                idx = size - i - 1;
        // request
        tmp.req.ben[byt] = 1'b1;
        tmp.req.wdt[byt] = transaction.req.wdt[idx];
        tmp.rsp.rdt[byt] = transaction.rsp.rdt[idx];
        // last byte in current transfer or entire transaction
        if ((byt == BUS_BEN) || (i == size-1)) begin
          // request signals
          tmp.req.frm = (i = size-1) ? 1'b0 : 1'b1;
          tmp.req.wen = transaction.req.wen;
          tmp.req.ndn = transaction.req.ndn;
          tmp.req.adr = transaction.req.adr + i*BUS_BEN;
          case (BUS.MOD)
            TCB_MOD_LOG_SIZE: begin
              tmp.req.siz = (size < BUS_BEN) ? $clog2(size) : BUS_MAX;
              tmp.req.ben = 'x;
            end
            TCB_MOD_BYTE_ENA: begin
              tmp.req.siz = 'x;
            end
          endcase
          // response
          tmp.rsp.sts = transaction.rsp.sts;
          // ID
          tmp.id = $sformatf("%s[%0d]", id, cnt);
          // add transfer to queue
          transfer_queue.push_back(tmp);
          cnt++;
          // clear transfer
          tmp = '{req: '{default: 'x}, rsp: '{default: 'x}, id: "", default: 0};
        end
      end
      //      $display("DEBUG: inside: transfer_queue.size() = %d", transfer_queue.size());
      return(cnt);
    endfunction: set_transaction

  //////////////////////////////////////////////////////////////////////////////
  // get transaction from transfer array
  //////////////////////////////////////////////////////////////////////////////

    // read/write response transaction of power of 2 size
    static function automatic int unsigned get_transaction (
      ref    transfer_queue_t transfer_queue,
      output transaction_t    transaction
    );
      // transaction data size
      int unsigned size = 0;  // transaction side (units/bytes)

      // write/read data queue
      logic [8-1:0] wdt [$];
      logic [8-1:0] rdt [$];

      // transfer counter
      int unsigned cnt = 0;
      transfer_t tmp;

      // request signals (first transfer)
      transaction.req.wen = transfer_queue[0].req.wen;
      transaction.req.ndn = transfer_queue[0].req.ndn;
      transaction.req.adr = transfer_queue[0].req.adr;

      // initialize response
      transaction.rsp.sts = '0;

      size = 0;
      do begin
        tmp = transfer_queue.pop_front();
        $display("DEBUG: tmp = %p", tmp);
        // request signals
        assert (tmp.req.wen == transaction.req.wen              ) else $warning("wen mismatch %p %p", tmp.req.wen, transaction.req.wen);
        assert (tmp.req.ndn == transaction.req.ndn              ) else $warning("ndn mismatch");
        assert (tmp.req.adr == transaction.req.adr + cnt*BUS_BEN) else $warning("adr mismatch");
        // response status
        transaction.rsp.sts |= tmp.rsp.sts;

        // mode logarithmic size vs. byte enable
        case (BUS.MOD)
          TCB_MOD_LOG_SIZE: begin
            int unsigned siz = tmp.req.siz;
            // data signals
            for (int unsigned i=0; i<2**siz; i++) begin
              int unsigned byt = i;
              wdt.push_back(tmp.req.wdt[byt]);
              rdt.push_back(tmp.rsp.rdt[byt]);
            end
            size += 2**siz;
          end
          TCB_MOD_BYTE_ENA: begin
            // data signals
            for (int unsigned i=0; i<BUS_BEN; i++) begin
              int unsigned byt = (i + tmp.req.adr[BUS_MAX-1:0]) % BUS_BEN;
              // endianness
              if (tmp.req.ndn ^ BUS.ORD) begin
                // request/response
                wdt.push_back(tmp.req.wdt[byt]);
                rdt.push_back(tmp.rsp.rdt[byt]);
              end else begin
                // request/response
                wdt.push_front(tmp.req.wdt[byt]);
                rdt.push_front(tmp.rsp.rdt[byt]);
              end
            end
          end
        endcase
        // increment transfer counter
        cnt++;
      end while (~tmp.req.frm);
      // apply data
      transaction.req.wdt = new[wdt.size()](wdt);
      transaction.rsp.rdt = new[rdt.size()](rdt);

      //      $display("DEBUG: transaction.rsp.rdt = %p", transaction.rsp.rdt);
      return(cnt);
    endfunction: get_transaction

  endclass: tcb_vip_transaction_c

endpackage: tcb_vip_transaction_pkg
