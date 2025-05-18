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
    parameter  bit  DEBUG = 1'b0
  ) extends tcb_vip_transfer_c #(
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
      logic [BUS_ADR-1:0] adr;
      logic       [8-1:0] wdt [];
    } transaction_req_t;

    // TCB transaction response structure
    typedef struct {
      // response
      logic       [8-1:0] rdt [];
      tcb_rsp_sts_t       sts;
    } transaction_rsp_t;

    // TCB transaction structure
    typedef struct {
      transaction_req_t req;
      transaction_rsp_t rsp;
    } transaction_t;

  //////////////////////////////////////////////////////////////////////////////
  // set transfer array from transaction
  //////////////////////////////////////////////////////////////////////////////

    // read/write request transaction of power of 2 size
    function automatic int unsigned set_transaction (
      ref   transfer_queue_t transfer_queue,
      input transaction_t    transaction,
      input string           id = ""
    );
      // write/read enable
      bit          wen;
      bit          ren;
      // write/read data linear size
      int unsigned wdt_size;
      int unsigned rdt_size;
      int unsigned     size;
      // write/read data array logarithmic siz
      int unsigned wdt_siz;
      int unsigned rdt_siz;
      // endianness
      int unsigned ndn;

      // transfer counter
      int unsigned cnt = 0;
      transfer_t tmp;

//      $display("DEBUG: transaction: %p", transaction);

      // write/read data array linear size
      wdt_size = transaction.req.wdt.size();
      rdt_size = transaction.rsp.rdt.size();
      // write/read data array logarithmic siz
      wdt_siz = $clog2(wdt_size);
      rdt_siz = $clog2(rdt_size);

      // if write/read data is available, write/read is enabled
      wen = (wdt_size > 0);
      ren = (rdt_size > 0);

//      $display("DEBUG: transaction.req.wdt.size() = %0d, wen = %0b", wdt_size, wen);
//      $display("DEBUG: transaction.rsp.rdt.size() = %0d, ren = %0b", rdt_size, ren);

      // check whether data array sizes are power of 2
      if (wen) assert (wdt_size == 2**wdt_siz) else $error("Write data array size is not a power of 2.");
      if (ren) assert (rdt_size == 2**rdt_siz) else $error("Read  data array size is not a power of 2.");

      case (BUS.CHN)
        TCB_CHN_HALF_DUPLEX: begin
          assert ((wen & ren) == 1'b0) else $error("Attempt to create swap transaction on half duplex bus.");
          if (wen)  size = wdt_size;
          else      size = rdt_size;
        end
        TCB_CHN_FULL_DUPLEX: begin
          if (wen & ren) begin
            // swap operation
            assert (wdt_size == rdt_size) else $error("Attempt to create swap transaction with mismatched write/read data size.");
          end
          if (wen)  size = wdt_size;
          else      size = rdt_size;
        end
        TCB_CHN_WRITE_ONLY : begin
          assert ( wen) else $error("Attempt to create write transaction of size 0.");
          assert (~ren) else $error("Attempt to create read  transaction on write only bus.");
          size = wdt_size;
        end
        TCB_CHN_READ_ONLY  : begin
          assert (~wen) else $error("Attempt to create write transaction on read only bus.");
          assert ( ren) else $error("Attempt to create read  transaction of size 0.");
          size = rdt_size;
        end
      endcase

      // endianness
      ndn = tcb.endianness(transaction.req.ndn);


//      $display("DEBUG: size=%0d", size);

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

      // loop over transaction data bytes
      tmp.req.ben = '0;
      for (int unsigned i=0; i<size; i++) begin
        // temporary variables
        int unsigned byt;  // transfer byte index
        int unsigned idx;  // transaction byte index
        int unsigned edg;  // edge byte inside data bus

        // endianness
        if (ndn)  idx = size-1-i;  //    big-endian (start with MSB end)
        else      idx =        i;  // little-endian (start with LSB end)
        // mode logarithmic size vs. byte enable
        case (BUS.MOD)
          TCB_MOD_LOG_SIZE:  byt =  idx                                   % BUS_BEN;  // all data bytes are LSB aligned
          TCB_MOD_BYTE_ENA:  byt = (i + transaction.req.adr[BUS_MAX-1:0]) % BUS_BEN;
        endcase
        // request
        if (wen) tmp.req.wdt[byt] = transaction.req.wdt[idx];
        if (ren) tmp.rsp.rdt[byt] = transaction.rsp.rdt[idx];
                 tmp.req.ben[byt] = 1'b1;
        // edge byte inside data bus
        if (PCK.BND == 0)  edg = (i == BUS_BEN-1);
        else               edg = BUS_BEN-1;  // TODO: use actual boundary

        // last byte in current transfer or entire transaction
        if (edg || (i == size-1)) begin
          // request signals
          tmp.req.frm = (i == size-1) ? 1'b0 : 1'b1;
          if (BUS.CHN == TCB_CHN_FULL_DUPLEX) begin
            tmp.req.wen = wen;
            tmp.req.ren = ren;
          end
          if (BUS.CHN == TCB_CHN_HALF_DUPLEX) begin
            tmp.req.wen = wen;
          end
          if (BUS.NDN == TCB_NDN_BI_NDN) begin
            tmp.req.ndn = ndn;
          end
          tmp.req.adr = transaction.req.adr + cnt*BUS_BEN;
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
          tmp = '{req: '{ben: '0, default: 'x}, rsp: '{default: 'x}, id: "", default: 0};
        end
      end
//      foreach (transfer_queue[i])
//      $display("DEBUG: inside: transfer_queue[%0d] = %p", i, transfer_queue[i]);
      return(cnt);
    endfunction: set_transaction

  //////////////////////////////////////////////////////////////////////////////
  // get transaction from transfer array
  //////////////////////////////////////////////////////////////////////////////

    // read/write response transaction of power of 2 size
    function automatic int unsigned get_transaction (
      ref    transfer_queue_t transfer_queue,
      output transaction_t    transaction
    );
      // transaction data size
      int unsigned size = 0;  // transaction side (units/bytes)

      // write/read enable
      bit           wen;
      bit           ren;
      // write/read data queue
      logic [8-1:0] wdt [$];
      logic [8-1:0] rdt [$];
      // endianness
      logic         ndn;

      // transfer counter
      int unsigned cnt = 0;
      transfer_t tmp;

      // write/read enable
      wen = tcb.write(transfer_queue[0].req.wen);
      ren = tcb.read (transfer_queue[0].req.wen, transfer_queue[0].req.ren);

      // endianness
      transaction.req.ndn = tcb.endianness(transfer_queue[0].req.ndn);

      // request signals (first transfer)
      transaction.req.adr = transfer_queue[0].req.adr;

      // initialize response
      transaction.rsp.sts = '0;

      size = 0;
      do begin
        tmp = transfer_queue.pop_front();
//        $display("DEBUG: tmp = %p", tmp);
        // request signals
        // read/write enable continuity checks
        case (BUS.CHN)
          TCB_CHN_HALF_DUPLEX: begin
            assert (tmp.req.wen == wen) else $error("wen continuity %0b %0b", tmp.req.wen, wen);
          end
          TCB_CHN_FULL_DUPLEX: begin
            assert (tmp.req.wen == wen) else $error("wen continuity %0b %0b", tmp.req.wen, wen);
            assert (tmp.req.ren == ren) else $error("ren continuity %0b %0b", tmp.req.ren, ren);
          end
        endcase
        // endianness continuity checks
        if (BUS.NDN == TCB_NDN_BI_NDN) begin
          assert (tmp.req.ndn == transaction.req.ndn) else $error("ndn continuity %0b %0b", tmp.req.ndn, transaction.req.ndn);
        end
        // TODO: address continuity depends on transfer type
        assert (tmp.req.adr == transaction.req.adr + cnt*BUS_BEN) else $error("adr continuity");
        // response status
        transaction.rsp.sts |= tmp.rsp.sts;

        // mode logarithmic size vs. byte enable
        case (BUS.MOD)
          TCB_MOD_LOG_SIZE: begin
            int unsigned siz = tmp.req.siz;
            // data signals
            for (int unsigned i=0; i<2**siz; i++) begin
              int unsigned byt = i;
              if (wen) wdt.push_back(tmp.req.wdt[byt]);
              if (ren) rdt.push_back(tmp.rsp.rdt[byt]);
            end
            size += 2**siz;
          end
          TCB_MOD_BYTE_ENA: begin
            // data signals
            for (int unsigned i=0; i<BUS_BEN; i++) begin
              int unsigned byt = (i + tmp.req.adr[BUS_MAX-1:0]) % BUS_BEN;
              if (tmp.req.ben[byt]) begin
                // endianness request/response data
                if (tmp.req.ndn ~^ BUS.ORD) begin
                  if (wen) wdt.push_back(tmp.req.wdt[byt]);
                  if (ren) rdt.push_back(tmp.rsp.rdt[byt]);
                end else begin
                  if (wen) wdt.push_front(tmp.req.wdt[byt]);
                  if (ren) rdt.push_front(tmp.rsp.rdt[byt]);
                end
              end
            end
          end
        endcase
        // increment transfer counter
        cnt++;
      end while (tmp.req.frm);
      // apply data
      transaction.req.wdt = new[wdt.size()](wdt);
      transaction.rsp.rdt = new[rdt.size()](rdt);

      //      $display("DEBUG: transaction.rsp.rdt = %p", transaction.rsp.rdt);
      return(cnt);
    endfunction: get_transaction

  endclass: tcb_vip_transaction_c

endpackage: tcb_vip_transaction_pkg
