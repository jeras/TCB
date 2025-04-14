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
    tcb_phy_t  PHY = TCB_PAR_PHY_DEF,
    type tcb_req_cmd_t = tcb_req_cmd_def_t,
    type tcb_rsp_sts_t = tcb_rsp_sts_def_t
  );

////////////////////////////////////////////////////////////////////////////////
// local parameters
////////////////////////////////////////////////////////////////////////////////

    // byte enable width
    localparam int unsigned PHY_BEN = PHY.DAT / PHY.UNT;

    // transfer size width calculation
    localparam int unsigned PHY_SIZ_LIN = $clog2(       PHY_BEN   );  // linear
    localparam int unsigned PHY_SIZ_LOG = $clog2($clog2(PHY_BEN)+1);  // logarithmic (default)
    // transfer size width selection
    localparam int unsigned PHY_SIZ = PHY_SIZ_LOG;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

    typedef virtual tcb_if #(
      .PHY           (PHY),
      .tcb_req_cmd_t (tcb_req_cmd_t),
      .tcb_rsp_sts_t (tcb_rsp_sts_t)
    ) tcb_vif_t;

    string MODE = "MON";
    tcb_vif_t tcb;

    //constructor
    function new(string MODE = "MON", tcb_vif_t tcb);
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
    typedef logic [PHY_BEN-1:0][PHY.UNT-1:0] data_byte_t;

    // created data for tests
    static function automatic data_byte_t data_test_f (
      input logic [PHY.UNT/2-1:0] val = 'x
    );
      for (int unsigned i=0; i<PHY_BEN; i++) begin
        data_test_f[i] = {val, i[PHY.UNT/2-1:0]};
      end
    endfunction: data_test_f

////////////////////////////////////////////////////////////////////////////////
// transfer
////////////////////////////////////////////////////////////////////////////////

    // TCB transfer request structure
    typedef struct {
      tcb_req_cmd_t                    cmd;  // command (optional)
      logic                            wen;  // write enable
      logic                            ndn;  // endianness
      logic [PHY.ADR-1:0]              adr;  // address
      logic [PHY_SIZ-1:0]              siz;  // logarithmic size
      logic                            uns;  // unsigned
      logic [PHY_BEN-1:0]              ben;  // byte enable
      logic [PHY_BEN-1:0][PHY.UNT-1:0] wdt;  // write data
    } transfer_request_t;

    // TCB transfer response structure
    typedef struct {
      logic [PHY_BEN-1:0][PHY.UNT-1:0] rdt;  // read data
      tcb_rsp_sts_t                    sts;  // status (optional)
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
      // request
      req: '{
        cmd: 'x,
        wen: 1'bx,
        ndn: 1'bx,
        adr: 'x,
        siz: 'x,
        uns: 'x,
        ben: 'x,
        wdt: 'x
      },
      // response
      rsp: '{
        rdt: 'x,
        sts: 'x
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
      //transfer_check = (trn_tst ==? (trn_ref ~^ trn_msk));
      transfer_check = 1'bx;
    endfunction: transfer_check

////////////////////////////////////////////////////////////////////////////////
// transfer request/response (enable pipelined transfers with full throughput)
////////////////////////////////////////////////////////////////////////////////

    // transfer request driver
    task automatic transfer_req_drv (
      input  transfer_request_t req,
      input  int unsigned       idl,
      output int unsigned       bpr
    );
      // request timing
      repeat (idl) @(posedge tcb.clk);
      // drive transfer
      #1;
      // handshake
      tcb.vld = 1'b1;
      // request
      tcb.req.cmd = req.cmd;
      tcb.req.wen = req.wen;
      tcb.req.ndn = req.ndn;
      tcb.req.adr = req.adr;
      tcb.req.siz = req.siz;
      tcb.req.uns = req.uns;
      tcb.req.ben = req.ben;
      tcb.req.wdt = req.wdt;
      // backpressure
      bpr = 0;
      do begin
        @(posedge tcb.clk);
        if (~tcb.rdy) bpr++;
      end while (~tcb.trn);
      // drive idle/undefined
      #1;
      // handshake
      tcb.vld = 1'b0;
      // request
      tcb.req.cmd = 'x;
      tcb.req.wen = 'x;
      tcb.req.ndn = 'x;
      tcb.req.adr = 'x;
      tcb.req.siz = 'x;
      tcb.req.uns = 'x;
      tcb.req.ben = 'x;
      tcb.req.wdt = 'x;
    endtask: transfer_req_drv

    // transfer response listener
    task automatic transfer_rsp_lsn (
      output transfer_response_t rsp
    );
      // wait for response
      do begin
        @(posedge tcb.clk);
      end while (~tcb.dly[tcb.PHY.DLY].ena);
      // response
      rsp.rdt = tcb.rsp.rdt;
      rsp.sts = tcb.rsp.sts;
    endtask: transfer_rsp_lsn

    // transfer request listener
    task automatic transfer_req_lsn (
      output transfer_request_t req,
      output int unsigned       idl,
      input  int unsigned       bpr
    );
      #1;
      tcb.rdy = 1'b0;
      // TODO: measure idle time
      idl = 0;
      // request
      if (bpr == 0) begin
        // ready
        tcb.rdy = 1'b1;
        // wait for transfer
        do begin
          @(posedge tcb.clk);
          idl += tcb.vld ? 0 : 1;
        end while (~tcb.trn);
      end else begin
        // backpressure
        for (int unsigned i=0; i<bpr; i+=(tcb.vld?1:0)) begin
          @(posedge tcb.clk);
          idl += tcb.vld ? 0 : 1;
        end
        // ready
        #1;
        tcb.rdy = 1'b1;
        // wait for transfer
        do begin
          @(posedge tcb.clk);
        end while (~tcb.trn);
      end
      req.cmd = tcb.req.cmd;
      req.wen = tcb.req.wen;
      req.ndn = tcb.req.ndn;
      req.adr = tcb.req.adr;
      req.siz = tcb.req.siz;
      req.uns = tcb.req.uns;
      req.ben = tcb.req.ben;
      req.wdt = tcb.req.wdt;
    endtask: transfer_req_lsn

    // transfer response driver
    task automatic transfer_rsp_drv (
      input  transfer_response_t rsp
    );
      // response
      tcb.rsp.rdt = rsp.rdt;
      tcb.rsp.sts = rsp.sts;
      // wait for response
      do begin
        @(posedge tcb.clk);
      end while (~tcb.dly[tcb.PHY.DLY].ena);
    endtask: transfer_rsp_drv

////////////////////////////////////////////////////////////////////////////////
// transaction sequence non-blocking API
////////////////////////////////////////////////////////////////////////////////

    // BUG: at DLY=0, there is a race condition between

    // request/response
    task automatic transfer_sequencer (
      inout  transfer_array_t transfer_array
    );
      fork
        begin: fork_req
          foreach (transfer_array[i]) begin
            case (MODE)
              "MAN": transfer_req_drv(transfer_array[i].req, transfer_array[i].idl, transfer_array[i].bpr);
              "MON": transfer_req_lsn(transfer_array[i].req, transfer_array[i].idl, transfer_array[i].bpr);
              "SUB": transfer_req_lsn(transfer_array[i].req, transfer_array[i].idl, transfer_array[i].bpr);
            endcase
          end
        end: fork_req
        begin: fork_rsp
          foreach (transfer_array[i]) begin
            case (MODE)
              "MAN": transfer_rsp_lsn(transfer_array[i].rsp);
              "MON": transfer_rsp_lsn(transfer_array[i].rsp);
              "SUB": transfer_rsp_drv(transfer_array[i].rsp);
            endcase
          end
        end: fork_rsp
      join
    endtask: transfer_sequencer

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
            $error("ERROR: Transaction address is not aligned to supported size. adr[%d:0]=%0b", PHY.ALN-1, adr_alw);
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
          transfer_array[i].req.uns = transaction_req.uns;
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

    task write8 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [1-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [1-1:0][PHY.UNT-1:0] rdt;
      transaction8(1'b1, adr, wdt, rdt, sts);
    endtask: write8

    task read8 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [1-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [1-1:0][PHY.UNT-1:0] wdt = 'x;
      transaction8(1'b0, adr, wdt, rdt, sts);
    endtask: read8

    task check8 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [1-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [1-1:0][PHY.UNT-1:0] tmp_wdt = 'x;
      logic [1-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                      tmp_sts;
      transaction8(1'b0, adr, tmp_wdt, tmp_rdt, tmp_sts);
      if (tmp_rdt !== rdt) $display("ERROR: %m: (rdt=8'h%2X) !== (dat=8'h%2X) mismatch.", tmp_rdt, rdt);
      if (tmp_sts !== sts) $display("ERROR: %m: (sts=1'b%1b) !== (sts=1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check8

    task write16 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [2-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [2-1:0][PHY.UNT-1:0] rdt;
      transaction16(1'b1, adr, wdt, rdt, sts);
    endtask: write16

    task read16 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [2-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [4-1:0][PHY.UNT-1:0] wdt = 'x;
      transaction16(1'b0, adr, wdt, rdt, sts);
    endtask: read16

    task check16 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [2-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [2-1:0][PHY.UNT-1:0] tmp_wdt = 'x;
      logic [2-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                      tmp_sts;
      transaction16(1'b0, adr, tmp_wdt, tmp_rdt, tmp_sts);
      if (tmp_rdt !== rdt) $display("ERROR: %m: (rdt=16'h%4X) !== ref(rdt=16'h%4X) mismatch.", tmp_rdt, rdt);
      if (tmp_sts !== sts) $display("ERROR: %m: (sts= 1'b%1b) !== ref(sts= 1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check16

    task write32 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [4-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [4-1:0][PHY.UNT-1:0] rdt;
      transaction32(1'b1, adr, wdt, rdt, sts);
    endtask: write32

    task read32 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [4-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [4-1:0][PHY.UNT-1:0] wdt = 'x;
      transaction32(1'b0, adr, wdt, rdt, sts);
    endtask: read32

    task check32 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [4-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [4-1:0][PHY.UNT-1:0] tmp_wdt = 'x;
      logic [4-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                      tmp_sts;
      transaction32(1'b0, adr, tmp_wdt, tmp_rdt, tmp_sts);
      if (tmp_rdt !== rdt) $display("ERROR: %m: (rdt=32'h%8X) !== ref(rdt=32'h%8X) mismatch.", tmp_rdt, rdt);
      if (tmp_sts !== sts) $display("ERROR: %m: (sts= 1'b%1b) !== ref(sts= 1'b%1b) mismatch.", tmp_sts, sts);
    endtask: check32

    task write64 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [8-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [8-1:0][PHY.UNT-1:0] rdt;
      transaction64(1'b1, adr, wdt, rdt, sts);
    endtask: write64

    task read64 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic  [8-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [8-1:0][PHY.UNT-1:0] wdt = 'x;
      transaction64(1'b0, adr, wdt, rdt, sts);
    endtask: read64

    task check64 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic  [8-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [8-1:0][PHY.UNT-1:0] tmp_wdt = 'x;
      logic [8-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                      tmp_sts;
      transaction64(1'b0, adr, tmp_wdt, tmp_rdt, tmp_sts);
      if (tmp_rdt !== rdt) $display("ERROR: %m: (rdt=64'h%16X) !== (dat=64'h%16X) mismatch.", tmp_rdt, rdt);
      if (tmp_sts !== sts) $display("ERROR: %m: (sts= 1'b%01b) !== (sts= 1'b%01b) mismatch.", tmp_sts, sts);
    endtask: check64

    task write128 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic [16-1:0][PHY.UNT-1:0] wdt,
      output logic                       sts
    );
      logic [16-1:0][PHY.UNT-1:0] rdt;
      transaction128(1'b1, adr, wdt, rdt, sts);
    endtask: write128

    task read128 (
      input  logic         [PHY.ADR-1:0] adr,
      output logic [16-1:0][PHY.UNT-1:0] rdt,
      output logic                       sts
    );
      logic [16-1:0][PHY.UNT-1:0] wdt = 'x;
      transaction128(1'b0, adr, wdt, rdt, sts);
    endtask: read128

    task check128 (
      input  logic         [PHY.ADR-1:0] adr,
      input  logic [16-1:0][PHY.UNT-1:0] rdt,
      input  logic                       sts
    );
      logic [16-1:0][PHY.UNT-1:0] tmp_wdt = 'x;
      logic [16-1:0][PHY.UNT-1:0] tmp_rdt;
      logic                       tmp_sts;
      transaction128(1'b0, adr, tmp_wdt, tmp_rdt, tmp_sts);
      if (tmp_rdt !== rdt) $display("ERROR: %m: (rdt=128'h%32X) !== (dat=128'h%32X) mismatch.", tmp_rdt, rdt);
      if (tmp_sts !== sts) $display("ERROR: %m: (sts=  1'b%01b) !== (sts=  1'b%01b) mismatch.", tmp_sts, sts);
    endtask: check128

  endclass: tcb_transfer_c

endpackage: tcb_vip_pkg
