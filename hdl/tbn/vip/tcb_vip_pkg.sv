////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) PacKaGe
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

////////////////////////////////////////////////////////////////////////////////
// TCB class
////////////////////////////////////////////////////////////////////////////////

  virtual class tcb_c #(
    // TCB widths
    int unsigned ABW = 32,       // address bus width
    int unsigned DBW = 32,       // data    bus width
    int unsigned SLW =       8,  // selection   width
    int unsigned BEW = DBW/SLW,  // byte enable width
    // other parameters
    tcb_mode_t   MOD = TCB_MEMORY,
    tcb_order_t  ORD = TCB_DESCENDING,
    tcb_align_t  LGN = TCB_ALIGNED
  );

    localparam int unsigned SZW = $clog2($clog2(BEW)+1);  // logarithmic size width

////////////////////////////////////////////////////////////////////////////////
// reference data for tests
////////////////////////////////////////////////////////////////////////////////

    // data organized into packed bytes
    typedef logic [BEW-1:0][SLW-1:0] data_byte_t;

    // created data for tests
    static function automatic data_byte_t data_test_f (
      input logic [SLW/2-1:0] val = 'x
    );
      for (int unsigned i=0; i<BEW; i++) begin
        data_test_f[i] = {val, i[SLW/2-1:0]};
      end
    endfunction: data_test_f

////////////////////////////////////////////////////////////////////////////////
// transfer
////////////////////////////////////////////////////////////////////////////////

    // TCB transfer request structure
    typedef struct {
      // request optional
      logic                    inc;  // incremented address
      logic                    rpt;  // repeated address
      logic                    lck;  // arbitration lock
      logic                    ndn;  // endianness
      // request
      logic                    wen;  // write enable
      logic          [ABW-1:0] adr;  // address
      logic          [SZW-1:0] siz;  // logarithmic size
      logic [BEW-1:0]          ben;  // byte enable
      logic [BEW-1:0][SLW-1:0] wdt;  // write data
    } transfer_request_t;

    // TCB transfer response structure
    typedef struct {
      // response
      logic [BEW-1:0][SLW-1:0] rdt;  // read data
      logic                    err;  // error
    } transfer_response_t;

    // TCB transfer structure
    typedef struct {
      // request/response
      transfer_request_t  req;  // request
      transfer_response_t rsp;  // response
      // timing idle/backpressure
      int unsigned        idl;  // idle
      int unsigned        bpr;  // backpressure
    } transfer_t;

    typedef transfer_t transfer_array_t [];

    // constants
    static const transfer_t TRANSFER_INIT = '{
      req: '{
        // request optional
        inc: 1'b0,
        rpt: 1'b0,
        lck: 1'b0,
        ndn: 1'bx,
        // request
        wen: 'x,
        adr: 'x,
        siz: 'x,
        ben: 'x,
        wdt: 'x
      },
      rsp: '{
        // response
        rdt: 'x,
        err: 'x
      },
      // timing idle/backpressure
      idl: 0,
      bpr: 0
    };

    // transfer equivalence check
    static function automatic logic transfer_check (
      // transfer_array
      input  transfer_t trn_tst,  // test
      input  transfer_t trn_ref,  // reference
      input  transfer_t trn_msk   // mask
    );
//      transfer_check = (trn_tst ==? (trn_ref ~^ trn_msk));
    endfunction: transfer_check

////////////////////////////////////////////////////////////////////////////////
// transaction
////////////////////////////////////////////////////////////////////////////////

    virtual class transaction_c #(
      // TCB widths
      int unsigned SIZ = BEW  // transaction size in bytes
    );

      // TCB transaction request structure
      typedef struct {
        // request
        logic                    wen;
        logic          [ABW-1:0] adr;
        logic [SIZ-1:0][SLW-1:0] wdt;
        // endianness
        tcb_endian_t             ndn;
      } transaction_request_t;

      // TCB transaction response structure
      typedef struct {
        // response
        logic [SIZ-1:0][SLW-1:0] rdt;
        logic                    err;
      } transaction_response_t;

      // TCB transaction structure
      typedef struct {
        transaction_request_t  req;
        transaction_response_t rsp;
      } transaction_t;

      // read/write request transaction of power of 2 size
      static function automatic transfer_array_t transaction_request (
        // TCB transaction structure
        transaction_request_t transaction
      );
        // temporary variables
        int unsigned byt;  // byte index
        int unsigned off;  // address offset
        // the requested transaction is organized into transfer_array
        transfer_array_t transfer_array;
        // number of transfer_array
        transfer_array = new[SIZ / BEW]('{default: TRANSFER_INIT});
        // check if the transfer meets size requirements
        if (SIZ != 2**$clog2(SIZ)) begin
          $error("ERROR: Transaction size is not power of 2.");
        end
        // check if the transfer meets alignment requirements
        if ((LGN == TCB_ALIGNED) && (transaction.adr % SIZ != 0)) begin
          $error("ERROR: Transaction address is not aligned to transaction size.");
        end
        for (int unsigned i=0; i<SIZ; i++) begin
          // address offset
          off = i % BEW;
          // request optional
          transfer_array[off].req.inc = 1'b0;
          transfer_array[off].req.rpt = 1'b0;
          transfer_array[off].req.lck = (i == SIZ-1) ? 1'b0 : 1'b1;
          transfer_array[off].req.ndn = transaction.ndn;
          // request
          transfer_array[off].req.wen = transaction.wen;
          transfer_array[off].req.adr = transaction.adr;
          // mode processor/memory
          if (MOD == TCB_REFERENCE) begin
            // all data bytes are LSB aligned
            byt = i;
          end else if (MOD == TCB_MEMORY) begin
            // all data bytes are LSB aligned
            byt = (i + transaction.adr) % BEW;
          end
          // order descending/ascending
          if (ORD == TCB_ASCENDING) begin
            byt = BEW - 1 - byt;
          end
          // request
          transfer_array[off].req.ben[byt] = 1'b1;
          // endianness
          if (transaction.ndn == TCB_LITTLE) begin
            transfer_array[off].req.wdt[byt] = transaction.wdt[          i];
          end else begin
            transfer_array[off].req.wdt[byt] = transaction.wdt[SIZ - 1 - i];
          end
        end
        return(transfer_array);
      endfunction: transaction_request

      // read/write response transaction of power of 2 size
      static function automatic transaction_response_t transaction_response (
        transfer_array_t transfer_array
      );
        // temporary variables
        int unsigned byt;  // byte index
        int unsigned off;  // address offset
        // transaction
        transaction_response_t transaction;
        // response
        transaction.err = 1'b0;
        for (int unsigned i=0; i<SIZ; i++) begin
          // address offset
          off = i % BEW;
          // mode processor/memory
          if (MOD == TCB_REFERENCE) begin
            // all data bytes are LSB aligned
            byt = i;
          end else if (MOD == TCB_MEMORY) begin
            // all data bytes are LSB aligned
            byt = (i + transfer_array[off].req.adr) % BEW;
          end
          // order descending/ascending
          if (ORD == TCB_ASCENDING) begin
            byt = BEW - 1 - byt;
          end
          // endianness
          if (transfer_array[off].req.ndn == TCB_LITTLE) begin
            transaction.rdt[          i] = transfer_array[off].rsp.rdt[byt];
          end else begin
            transaction.rdt[SIZ - 1 - i] = transfer_array[off].rsp.rdt[byt];
          end
          transaction.err               |= transfer_array[off].rsp.err;
        end
        return(transaction);
      endfunction: transaction_response

    endclass: transaction_c

  endclass: tcb_c

////////////////////////////////////////////////////////////////////////////////
// packet class
////////////////////////////////////////////////////////////////////////////////

  virtual class packet_c #(
    // TCB widths
    int unsigned SLW = 8,  // selection width (byte size)
    int unsigned NUM = 4   // number of bytes
  );

    // type definitions
    typedef logic [NUM-1:0][SLW-1:0] dat_t          ;  //   packed byte array
//  typedef logic          [SLW-1:0] pkt_t [NUM-1:0];  // unpacked byte array
    typedef logic          [SLW-1:0] pkt_t [];         // dynamic  byte array

    // convert dynamic array
    static function automatic dat_t dat (
      pkt_t pkt
    );
      for (int unsigned i=0; i<1; i++)  dat[i] = pkt[i];
    endfunction: dat

    // convert dynamic array
    static function automatic pkt_t pkt (
      dat_t dat
    );
      pkt = new[NUM];
      for (int unsigned i=0; i<1; i++)  pkt[i] = dat[i];
    endfunction: pkt

  endclass: packet_c

endpackage: tcb_vip_pkg
