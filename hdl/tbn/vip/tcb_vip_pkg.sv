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
    } request_t;
    /* verilator lint_on UNPACKED */

    /* verilator lint_off UNPACKED */
    // TCB response structure
    typedef struct {
      // response
      logic [BEW-1:0][SLW-1:0] rdt;  // read data
      logic                    err;  // error
    } response_t;
    /* verilator lint_on UNPACKED */

    /* verilator lint_off UNPACKED */
    // TCB transaction structure
    typedef struct {
      // request/response
      request_t    req;  // request
      response_t   rsp;  // response
      // timing idle/backpressure
      int unsigned idl;  // idle
      int unsigned bpr;  // backpressure
    } transaction_t;
    /* verilator lint_on UNPACKED */

    typedef transaction_t transactions_t [];

    // constants
    static const transaction_t TRANSACTION_INIT = '{
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
/*
    virtual class access_c #(
      // TCB widths
      int unsigned SIZ = BEW  // access size in bytes
    );


      // read/write access of any size
      function automatic transactions_t access_req (
        // request
        input  logic               wen,
        input  logic [tcb.ABW-1:0] adr,
        ref    logic [tcb.SLW-1:0] wdt [SIZ]
      );
        transaction_t transactions [];
        // address offset from native bus allignment
        int unsigned off = adr % BEW;
        // number of transactions
        if (SIZ < BEW) begin
          transactions = new[1];
          transactions = '{default: TRANSACTION_INIT};
          // request optional
          transactions[0].inc = 1'b0;
          transactions[0].rpt = 1'b0;
          transactions[0].lck = 1'b0;
          // request
          transactions[0].wen = wen;
          transactions[0].adr = adr;
          transactions[0].ben = '0;
          for (int unsigned b=0; b<SIZ; b++) begin
            transactions[0].ben[(b+off)%BEW] = 1'b1;
            transactions[0].wdt[(b+off)%BEW] = wdt[b];
          end
          // timing idle (no backpressure)
          transactions[0].idl = 0;
        end else begin
          int unsigned num;
          num = (SIZ / tcb.BEW);
          transactions = new[num];
          transactions = '{default: TRANSACTION_INIT};
          for (int unsigned i=0; i<num; i++) begin
            // request optional
            transactions[i].inc = 1'b0;
            transactions[i].rpt = 1'b0;
            transactions[i].lck = (i == num) ? 1'b0 : 1'b1;
            // request
            transactions[i].wen = wen;
            transactions[i].adr = adr + i * tcb.BEW;
            for (int unsigned b=0; b<tcb.BEW; b++) begin
              transactions[i].ben[(b+off)%BEW] = 1'b1;
              transactions[i].wdt[(b+off)%BEW] = wdt[b + i * tcb.BEW];
            end
            // timing idle (no backpressure)
            transactions[i].idl = 0;
          end
        end
        return(transactions);
      endfunction: access_req

//      function automatic transactions_t access_rsp (
//        // response
//        ref    logic [tcb.SLW-1:0] wdt [SIZ],
//        output logic               err
//      );
//        // number of transactions
//        if (SIZ < BEW) begin
//        end else begin
//          err = 1'b0;
//          for (int unsigned i=0; i<num; i++) begin
//            for (int unsigned b=0; b<tcb.BEW; b++) begin
//              dat[b + i * tcb.BEW] = transactions[i].rdt[b];
//              err                 |= transactions[i].err;
//            end
//          end
//        end
//      endfunction: access_rsp

    endclass: access_c
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