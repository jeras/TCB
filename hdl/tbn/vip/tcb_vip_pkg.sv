////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verifivation IP) PacKaGe
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
// transacion
////////////////////////////////////////////////////////////////////////////////

    /* verilator lint_off UNPACKED */
    // TCB transaction structure
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
      // response
      logic [BEW-1:0][SLW-1:0] rdt;  // read data
      logic                    err;  // error
      // timing idle/backpressure
      int unsigned             idl;  // idle
      int unsigned             bpr;  // backpressure
    } transaction_t;
    /* verilator lint_on UNPACKED */

    // constants
    static const transaction_t TRANSACTION_INIT = '{
      // request optional
      inc: 1'b0,
      rpt: 1'b0,
      lck: 1'b0,
      // request
      wen: 'x,
      adr: 'x,
      siz: 'x,
      ben: 'x,
      wdt: 'x,
      // response
      rdt: 'x,
      err: 'x,
      // timing idle/backpressure
      idl: 0,
      bpr: 0
    };

    // transaction equivalence check
    static function automatic logic transaction_check (
      // transactions
      input  transaction_t trn_tst,  // test
      input  transaction_t trn_ref,  // reference
      input  transaction_t trn_msk   // mask
    );
//      transaction_check = (trn_tst ==? (trn_ref ~^ trn_msk));
    endfunction: transaction_check

////////////////////////////////////////////////////////////////////////////////
// access
////////////////////////////////////////////////////////////////////////////////

    virtual class access_c #(
      // TCB widths
      int unsigned SIZ = BEW  // access size in bytes
    );

/*
      // read/write access of any size
      task automatic access (
        // request
        input  logic               wen,
        input  logic [tcb.ABW-1:0] adr,
        ref    logic [tcb.SLW-1:0] dat [],
        // response
        output logic               err
      );
        int unsigned num;
        tcb_s::transaction_t transactions [];
        int unsigned idx_trn = 0;
        int unsigned idx_ben = adr % tcb.BEW;
        case (tcb.MIS)
          // missalligned accesses are split into alligned accesses
          1'b0: begin
          end
          // missalligned access is supported
          1'b1: begin
            // the number of transactions is
            // = the access size + missalligned part of the address
            // / divided by bus native byte enable width
            // + plus one, if therr is a reinder to the division.
            num = siz;
            num = (num / tcb.BEW);
            // local transactions
            transactions = new[num];
    //        $display("Transaction start.");
            // mapping
            transactions = '{default: tcb_s::TRANSACTION_INIT};
            for (int unsigned i=0; i<siz; i++) begin
              // request optional
              transactions[idx_trn].inc = 1'b0;
              transactions[idx_trn].rpt = 1'b0;
              transactions[idx_trn].lck = (idx_trn < num) ? 1'b1 : 1'b0;
              // request
              transactions[idx_trn].wen = wen;
              transactions[idx_trn].adr = adr + idx_trn * tcb.BEW;
              transactions[idx_trn].ben[idx_ben] = 1'b1;
              transactions[idx_trn].wdt[idx_ben] = dat[i];
              // timing idle/backpressure
              transactions[idx_trn].idl = 0;
              // index increments
              idx_ben = (idx_ben + 1) % tcb.BEW;
              if (idx_ben == adr % tcb.BEW) idx_trn++;
            end
          end
        endcase
        // transaction
        sequencer(transactions);
      endtask: access
*/
    endclass: access_c

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