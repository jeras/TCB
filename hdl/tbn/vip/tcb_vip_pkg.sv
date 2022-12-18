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
    int unsigned BEW = DBW/SLW   // byte enable width
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
      logic                    rpt;  // repeat access
      logic                    lck;  // arbitration lock
      // request
      logic                    wen;  // write enable
      logic          [ABW-1:0] adr;  // address
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
      rpt: 1'b0,
      lck: 1'b0,
      // request
      wen: 'x,
      adr: 'x,
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