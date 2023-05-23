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

  class tcb_transfer_c #(
    // TCB widths
    int unsigned ABW = 32,       // address bus width
    int unsigned DBW = 32,       // data    bus width
    int unsigned SLW =       8,  // selection   width
    int unsigned BEW = DBW/SLW,  // byte enable width
    // other parameters
    tcb_mode_t   MOD = TCB_REFERENCE,
    tcb_order_t  ORD = TCB_DESCENDING,
    tcb_align_t  LGN = TCB_ALIGNED
  );

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

    localparam int unsigned SZW = $clog2($clog2(BEW)+1);  // logarithmic size width

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

    string MODE = "MON";
    virtual tcb_if tcb;

    //constructor
    function new(string MODE = "MON", virtual tcb_if tcb);
      this.MODE = MODE;
      this.tcb = tcb;
      // initialization
      case (MODE)
        // manager
        "MAN": begin
          // initialize to idle state
          tcb.vld = 1'b0;
        end
        // monitor
        "MON": begin
        end
        // subordinate
        "SUB": begin
          // initialize to idle state
          tcb.rdy = 1'b0;
        end
      endcase
    endfunction: new

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
// transfer request/response (enable pipelined transfers with full throughput)
////////////////////////////////////////////////////////////////////////////////

  // transfer request driver
  task automatic transfer_req_drv (
    inout  transfer_t seq
  );
    // request timing
    repeat (seq.idl) @(posedge tcb.clk);
    // drive transfer
    #1;
    // handshake
    tcb.vld = 1'b1;
    // request optional
    tcb.req.inc = seq.req.inc;
    tcb.req.rpt = seq.req.rpt;
    tcb.req.lck = seq.req.lck;
    tcb.req.ndn = seq.req.ndn;
    // request
    tcb.req.wen = seq.req.wen;
    tcb.req.adr = seq.req.adr;
    tcb.req.siz = seq.req.siz;
    tcb.req.ben = seq.req.ben;
    tcb.req.wdt = seq.req.wdt;
    // backpressure
    seq.bpr = 0;
    do begin
      @(posedge tcb.clk);
      if (~tcb.rdy) seq.bpr++;
    end while (~tcb.trn);
    // drive idle/undefined
    #1;
    // handshake
    tcb.vld = 1'b0;
    // request optional
    tcb.req.inc = 'x;
    tcb.req.rpt = 'x;
    tcb.req.lck = 'x;
    tcb.req.ndn = 'x;
    // request
    tcb.req.wen = 'x;
    tcb.req.adr = 'x;
    tcb.req.siz = 'x;
    tcb.req.ben = 'x;
    tcb.req.wdt = 'x;
  endtask: transfer_req_drv

  // transfer response listener
  task automatic transfer_rsp_lsn (
    inout  transfer_t seq
  );
    // wait for response
    do begin
      @(posedge tcb.clk);
    end while (~tcb.dly[tcb.DLY].ena);
    // response
    seq.rsp.rdt = tcb.rsp.rdt;
    seq.rsp.err = tcb.rsp.err;
  endtask: transfer_rsp_lsn

  // transfer request listener
  task automatic transfer_req_lsn (
    inout  transfer_t seq
  );
    #1;
    tcb.rdy = 1'b0;
    // TODO: measure idle time
    seq.idl = 0;
    // request
    if (seq.bpr == 0) begin
      // ready
      tcb.rdy = 1'b1;
      // wait for transfer
      do begin
        @(posedge tcb.clk);
        seq.idl += tcb.vld ? 0 : 1;
      end while (~tcb.trn);
    end else begin
      // backpressure
      for (int unsigned i=0; i<seq.bpr; i+=(tcb.vld?1:0)) begin
        @(posedge tcb.clk);
        seq.idl += tcb.vld ? 0 : 1;
      end
      // ready
      #1;
      tcb.rdy = 1'b1;
      // wait for transfer
      do begin
        @(posedge tcb.clk);
      end while (~tcb.trn);
    end
    // request optional
    seq.req.inc = tcb.req.inc;
    seq.req.rpt = tcb.req.rpt;
    seq.req.lck = tcb.req.lck;
    seq.req.ndn = tcb.req.ndn;
    // request
    seq.req.wen = tcb.req.wen;
    seq.req.adr = tcb.req.adr;
    seq.req.siz = tcb.req.siz;
    seq.req.ben = tcb.req.ben;
    seq.req.wdt = tcb.req.wdt;
  endtask: transfer_req_lsn

  // transfer response driver
  task automatic transfer_rsp_drv (
    inout  transfer_t seq
  );
    // response
    tcb.rsp.rdt = seq.rsp.rdt;
    tcb.rsp.err = seq.rsp.err;
    // wait for response
    do begin
      @(posedge tcb.clk);
    end while (~tcb.dly[tcb.DLY].ena);
  endtask: transfer_rsp_drv

////////////////////////////////////////////////////////////////////////////////
// transaction sequence non-blocking API
////////////////////////////////////////////////////////////////////////////////

  // request/response
  task automatic transfer_sequencer (
    inout  transfer_array_t transfer_array
  );
    fork
      begin: fork_req
        foreach (transfer_array[i]) begin
          case (MODE)
            "MAN": transfer_req_drv(transfer_array[i]);
            "MON": transfer_req_lsn(transfer_array[i]);
            "SUB": transfer_req_lsn(transfer_array[i]);
          endcase 
        end
      end: fork_req
      begin: fork_rsp
        foreach (transfer_array[i]) begin
          case (MODE)
            "MAN": transfer_rsp_lsn(transfer_array[i]);
            "MON": transfer_rsp_lsn(transfer_array[i]);
            "SUB": transfer_rsp_drv(transfer_array[i]);
          endcase 
        end
      end: fork_rsp
    join
  endtask: transfer_sequencer

////////////////////////////////////////////////////////////////////////////////
// transaction class
////////////////////////////////////////////////////////////////////////////////

    virtual class tcb_transaction_c #(
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
        int unsigned len;
        transfer_array_t transfer_array;
        // number of transfer_array
        len = SIZ / BEW + (SIZ % BEW ? 1 : 0);
        $display ("DEBUG: SIZ = %d, BEW = %d, len = %d", SIZ, BEW, len);
        transfer_array = new[len];
//        transfer_array = new[len]('{default: super.TRANSFER_INIT});
        // check if the transfer meets size requirements
        if (SIZ != 2**$clog2(SIZ)) begin
          $error("ERROR: Transaction size is not power of 2.");
        end
        // check if the transfer meets alignment requirements
        if ((LGN == TCB_ALIGNED) && (transaction.adr % SIZ != 0)) begin
          $error("ERROR: Transaction address is not aligned to transaction size.");
        end
        // control and address signals
        for (int unsigned i=0; i<len; i++) begin
          // request optional
          transfer_array[i].req.inc = 1'b0;
          transfer_array[i].req.rpt = 1'b0;
          transfer_array[i].req.lck = (i == len-1) ? 1'b0 : 1'b1;
          transfer_array[i].req.ndn = transaction.ndn;
          // request
          transfer_array[i].req.wen = transaction.wen;
          transfer_array[i].req.adr = transaction.adr;
          transfer_array[i].req.ben = '0;
          transfer_array[i].req.siz = '0;
        end
        // data signals
        for (int unsigned i=0; i<SIZ; i++) begin
          // address offset
          off = i / BEW;
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
        int unsigned len;
        transaction_response_t transaction;
        // data signals
        for (int unsigned i=0; i<SIZ; i++) begin
          // address offset
          off = i / BEW;
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

    endclass: tcb_transaction_c

////////////////////////////////////////////////////////////////////////////////
// transaction
////////////////////////////////////////////////////////////////////////////////

    task automatic transaction8 (
      // request
      input  logic                            wen,
      input  logic              [tcb.ABW-1:0] adr,
      input  logic       [1-1:0][tcb.SLW-1:0] wdt,
      // response
      output logic       [1-1:0][tcb.SLW-1:0] rdt,
      output logic                            err,
      // endianness
      input  tcb_endian_t                     ndn = TCB_LITTLE
    );
      transfer_array_t transfer_array;
      typedef tcb_transaction_c #(1) tcb_transaction_p;
      tcb_transaction_p::transaction_t transaction;
      // request
      transaction.req = '{wen: wen, adr: adr, wdt: wdt, ndn: ndn};
      transfer_array = tcb_transaction_p::transaction_request(transaction.req);
      // transaction
      transfer_sequencer(transfer_array);
      // response
      transaction.rsp = tcb_transaction_p::transaction_response(transfer_array);
      // cleanup
      transfer_array.delete;
      // outputs
      rdt = transaction.rsp.rdt;
      err = transaction.rsp.err;
    endtask: transaction8

    task automatic transaction16 (
      // request
      input  logic                            wen,
      input  logic              [tcb.ABW-1:0] adr,
      input  logic       [2-1:0][tcb.SLW-1:0] wdt,
      // response
      output logic       [2-1:0][tcb.SLW-1:0] rdt,
      output logic                            err,
      // endianness
      input  tcb_endian_t                     ndn = TCB_LITTLE
    );
      transfer_array_t transfer_array;
      typedef tcb_transaction_c #(2) tcb_transaction_p;
      tcb_transaction_p::transaction_t transaction;
      // request
      transaction.req = '{wen: wen, adr: adr, wdt: wdt, ndn: ndn};
      transfer_array = tcb_transaction_p::transaction_request(transaction.req);
      // transaction
      transfer_sequencer(transfer_array);
      // response
      transaction.rsp = tcb_transaction_p::transaction_response(transfer_array);
      // cleanup
      transfer_array.delete;
      // outputs
      rdt = transaction.rsp.rdt;
      err = transaction.rsp.err;
    endtask: transaction16

    task automatic transaction32 (
      // request
      input  logic                            wen,
      input  logic              [tcb.ABW-1:0] adr,
      input  logic       [4-1:0][tcb.SLW-1:0] wdt,
      // response
      output logic       [4-1:0][tcb.SLW-1:0] rdt,
      output logic                            err,
      // endianness
      input  tcb_endian_t                     ndn = TCB_LITTLE
    );
      transfer_array_t transfer_array;
      typedef tcb_transaction_c #(4) tcb_transaction_p;
      tcb_transaction_p::transaction_t transaction;
      // request
      transaction.req = '{wen: wen, adr: adr, wdt: wdt, ndn: ndn};
      transfer_array = tcb_transaction_p::transaction_request(transaction.req);
      // transaction
      transfer_sequencer(transfer_array);
      // response
      transaction.rsp = tcb_transaction_p::transaction_response(transfer_array);
      // cleanup
      transfer_array.delete;
      // outputs
      rdt = transaction.rsp.rdt;
      err = transaction.rsp.err;
    endtask: transaction32

    task write8 (
      input  logic         [tcb.ABW-1:0] adr,
      input  logic  [1-1:0][tcb.SLW-1:0] wdt,
      output logic                       err
    );
      logic [1-1:0][tcb.SLW-1:0] rdt;
      transaction8(1'b1, adr, wdt, rdt, err);
    endtask: write8

    task read8 (
      input  logic         [tcb.ABW-1:0] adr,
      output logic  [1-1:0][tcb.SLW-1:0] rdt,
      output logic                       err
    );
      logic [1-1:0][tcb.SLW-1:0] wdt = 'x;
      transaction8(1'b0, adr, wdt, rdt, err);
    endtask: read8

    task write16 (
      input  logic         [tcb.ABW-1:0] adr,
      input  logic  [2-1:0][tcb.SLW-1:0] wdt,
      output logic                       err
    );
      logic [2-1:0][tcb.SLW-1:0] rdt;
      transaction16(1'b1, adr, wdt, rdt, err);
    endtask: write16

    task read16 (
      input  logic         [tcb.ABW-1:0] adr,
      output logic  [2-1:0][tcb.SLW-1:0] rdt,
      output logic                       err
    );
      logic [4-1:0][tcb.SLW-1:0] wdt = 'x;
      transaction16(1'b0, adr, wdt, rdt, err);
    endtask: read16

    task write32 (
      input  logic         [tcb.ABW-1:0] adr,
      input  logic  [4-1:0][tcb.SLW-1:0] wdt,
      output logic                       err
    );
      logic [4-1:0][tcb.SLW-1:0] rdt;
      transaction32(1'b1, adr, wdt, rdt, err);
    endtask: write32

    task read32 (
      input  logic         [tcb.ABW-1:0] adr,
      output logic  [4-1:0][tcb.SLW-1:0] rdt,
      output logic                       err
    );
      logic [4-1:0][tcb.SLW-1:0] wdt = 'x;
      transaction32(1'b0, adr, wdt, rdt, err);
    endtask: read32
/*
    task write64 (
      input  logic         [tcb.ABW-1:0] adr,
      input  logic  [8-1:0][tcb.SLW-1:0] wdt,
      output logic                       err
    );
      logic [tcb.SLW-1:0] dat [];
      dat = new[8];
      for (int unsigned i=0; i<8; i++)  dat[i] = wdt[i];
      access_man (8, 1'b1, adr, dat, err);
    endtask: write64

    task read64 (
      input  logic         [tcb.ABW-1:0] adr,
      output logic  [8-1:0][tcb.SLW-1:0] rdt,
      output logic                       err
    );
      logic [tcb.SLW-1:0] dat [];
      dat = new[8];
      access_man (8, 1'b0, adr, dat, err);
      for (int unsigned i=0; i<8; i++)  rdt[i] = dat[i];
    endtask: read64

    task write128 (
      input  logic         [tcb.ABW-1:0] adr,
      input  logic [16-1:0][tcb.SLW-1:0] wdt,
      output logic                       err
    );
      logic [tcb.SLW-1:0] dat [];
      dat = new[16];
      for (int unsigned i=0; i<16; i++)  dat[i] = wdt[i];
      access_man (16, 1'b1, adr, dat, err);
    endtask: write128

    task read128 (
      input  logic         [tcb.ABW-1:0] adr,
      output logic [16-1:0][tcb.SLW-1:0] rdt,
      output logic                       err
    );
      logic [tcb.SLW-1:0] dat [];
      dat = new[16];
      access_man (16, 1'b0, adr, dat, err);
      for (int unsigned i=0; i<16; i++)  rdt[i] = dat[i];
    endtask: read128
*/
  endclass: tcb_transfer_c

endpackage: tcb_vip_pkg
