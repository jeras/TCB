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
    int unsigned SZW = $clog2($clog2(BEW)+1)  // logarithmic size width
  );

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
    endfunction: data_test_f;

////////////////////////////////////////////////////////////////////////////////
// transfer
////////////////////////////////////////////////////////////////////////////////

    // TCB request structure
    typedef struct {
      // request optional
      logic                    inc;  // incremented address
      logic                    rpt;  // repeated address
      logic                    lck;  // arbitration lock
      // request
      logic                    wen;  // write enable
      logic          [ABW-1:0] adr;  // address
      logic          [SZW-1:0] siz;  // logarithmic size
      logic [BEW-1:0]          ben;  // byte enable
      logic [BEW-1:0][SLW-1:0] wdt;  // write data
    } transfer_request_t;

    // TCB response structure
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

/*
    virtual class transaction_c #(
      // TCB widths
      int unsigned SIZ = BEW  // transaction size in bytes
    );

      // TCB transaction structure
      typedef struct {
        // data size in bytes
        int unsigned             siz;
        // request
        logic                    wen;
        logic          [ABW-1:0] adr;
        logic [BEW-1:0][SLW-1:0] dat;
        // response
        logic                    err;
        // mode
        tcb_endian_t             ndn;
      } transaction_t;

      // manager read/write transaction of power of 2 size
      task automatic transaction_man (
        // data size
        input  int unsigned        siz,  // size in bytes
        // request
        input  logic               wen,
        input  logic [tcb.ABW-1:0] adr,
        ref    logic [tcb.SLW-1:0] dat [],
        // response
        output logic               err,
        // mode
        input  tcb_endian_t        endian = TCB_LITTLE
      );
        // temporary variables
        int unsigned byt;  // byte index
        int unsigned off;  // address offset
        // the requested transaction is organized into transfer_array
        transfer_array_t transfer_array;
        // number of transfer_array
        transfer_array = new[siz / tcb.BEW]('{default: TRANSFER_INIT});
        // check if the transfer meets size requirements
        if (siz != 2**$clog2(siz)) begin
          $error("ERROR: Transaction size is not power of 2.");
        end
        // check if the transfer meets alignment requirements
        if ((tcb.LGN == TCB_ALIGNED) && (adr % siz != 0)) begin
          $error("ERROR: Transaction address is not aligned to transaction size.");
        end
        for (int unsigned i=0; i<siz; i++) begin
          // address offset
          off = i % tcb.BEW;
          // request optional
          transfer_array[off].req.inc = 1'b0;
          transfer_array[off].req.rpt = 1'b0;
          transfer_array[off].req.lck = (i == siz-1) ? 1'b0 : 1'b1;
          // request
          transfer_array[off].req.wen = wen;
          transfer_array[off].req.adr = adr;
          // mode processor/memory
          if (tcb.MOD == TCB_PROCESSOR) begin
            // all data bytes are LSB aligned
            byt = i;
          end else if (tcb.MOD == TCB_MEMORY) begin
            // all data bytes are LSB aligned
            byt = (i + adr) % tcb.BEW;
          end
          // order descending/ascending
          if (tcb.ORD == TCB_ASCENDING) begin
            byt = tcb.BEW - 1 - byt;
          end
          // request
          transfer_array[off].req.ben[byt] = 1'b1;
          // endianness
          if (endian == TCB_LITTLE) begin
            transfer_array[off].req.wdt[byt] = dat[          i];
          end else begin
            transfer_array[off].req.wdt[byt] = dat[siz - 1 - i];
          end
        end
        // transaction
        sequencer(transfer_array);
        // response
        err = 1'b0;
        for (int unsigned i=0; i<siz; i++) begin
          // address offset
          off = i % tcb.BEW;
          // mode processor/memory
          if (tcb.MOD == TCB_PROCESSOR) begin
            // all data bytes are LSB aligned
            byt = i;
          end else if (tcb.MOD == TCB_MEMORY) begin
            // all data bytes are LSB aligned
            byt = (i + adr) % tcb.BEW;
          end
          // order descending/ascending
          if (tcb.ORD == TCB_ASCENDING) begin
            byt = tcb.BEW - 1 - byt;
          end
          // endianness
          if (endian == TCB_LITTLE) begin
            dat[          i] = transfer_array[off].rsp.rdt[byt];
          end else begin
            dat[siz - 1 - i] = transfer_array[off].rsp.rdt[byt];
          end
          err               |= transfer_array[off].rsp.err;
        end
      endtask: transaction_man

    endclass: transaction_c
*/
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