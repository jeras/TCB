////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) transfer PacKaGe
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

package tcb_vip_transfer_pkg;

  import tcb_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// TCB class
////////////////////////////////////////////////////////////////////////////////

  class tcb_vip_transfer_c #(
    parameter       tcb_phy_t PHY = TCB_PAR_PHY_DEF,
    parameter  type tcb_req_cmd_t = tcb_req_cmd_def_t,
    parameter  type tcb_rsp_sts_t = tcb_rsp_sts_def_t
  );

  //////////////////////////////////////////////////////////////////////////////
  // local parameters
  //////////////////////////////////////////////////////////////////////////////

    // byte enable width (number of units inside data)
    localparam int unsigned PHY_BEN = PHY.DAT / PHY.UNT;

    // offset width (number of address bits defining the offset of units inside data)
    localparam int unsigned PHY_OFF = $clog2(PHY_BEN);

    // logarithmic transfer size width
    localparam int unsigned PHY_SIZ = $clog2(PHY_OFF+1);

  //////////////////////////////////////////////////////////////////////////////
  // virtual interface
  //////////////////////////////////////////////////////////////////////////////

    // virtual interface type definition
    typedef virtual tcb_if #(
      .PHY           (PHY),
      .tcb_req_cmd_t (tcb_req_cmd_t),
      .tcb_rsp_sts_t (tcb_rsp_sts_t)
    ) tcb_vif_t;

    // virtual interface instance
    tcb_vif_t tcb;

    // direction
    string DIR = "";

    //constructor
    function new(
      string DIR = "MON",
      tcb_vif_t tcb
    );
      this.DIR = DIR;
      this.tcb = tcb;
      // initialization
      case (DIR)
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

  //////////////////////////////////////////////////////////////////////////////
  // reference data for tests
  //////////////////////////////////////////////////////////////////////////////

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

  //////////////////////////////////////////////////////////////////////////////
  // transfer
  //////////////////////////////////////////////////////////////////////////////

    // TCB transfer request structure
    typedef struct {
      tcb_req_cmd_t                    cmd;  // command (optional)
      logic                            wen;  // write enable
      logic                            ndn;  // endianness
      logic [PHY.ADR-1:0]              adr;  // address
      logic [PHY_SIZ-1:0]              siz;  // logarithmic size
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

  //////////////////////////////////////////////////////////////////////////////
  // transfer request/response (enable pipelined transfers with full throughput)
  //////////////////////////////////////////////////////////////////////////////

    // transfer request driver
    task automatic transfer_req_drv (
      input  transfer_request_t req,
      input  int unsigned       idl,
      output int unsigned       bpr
    );
      // request timing
      repeat (idl) @(posedge tcb.clk);
      // drive transfer
      // handshake
      tcb.vld <= 1'b1;
      // request
      tcb.req.cmd <= req.cmd;
      tcb.req.wen <= req.wen;
      tcb.req.ndn <= req.ndn;
      tcb.req.adr <= req.adr;
      tcb.req.siz <= req.siz;
      tcb.req.ben <= req.ben;
      tcb.req.wdt <= req.wdt;
      // backpressure
      bpr = 0;
      do begin
        @(posedge tcb.clk);
        if (~tcb.rdy) bpr++;
      end while (~tcb.trn);
      // drive idle/undefined
      // handshake
      tcb.vld <= 1'b0;
      // request
      tcb.req.cmd <= 'x;
      tcb.req.wen <= 'x;
      tcb.req.ndn <= 'x;
      tcb.req.adr <= 'x;
      tcb.req.siz <= 'x;
      tcb.req.ben <= 'x;
      tcb.req.wdt <= 'x;
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
      rsp.rdt <= tcb.rsp.rdt;
      rsp.sts <= tcb.rsp.sts;
    endtask: transfer_rsp_lsn

    // transfer request listener
    task automatic transfer_req_lsn (
      output transfer_request_t req,
      output int unsigned       idl,
      input  int unsigned       bpr
    );
      tcb.rdy <= 1'b0;
      // TODO: measure idle time
      idl = 0;
      // request
      if (bpr == 0) begin
        // ready
        tcb.rdy <= 1'b1;
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
        tcb.rdy <= 1'b1;
        // wait for transfer
        do begin
          @(posedge tcb.clk);
        end while (~tcb.trn);
      end
      req.cmd <= tcb.req.cmd;
      req.wen <= tcb.req.wen;
      req.ndn <= tcb.req.ndn;
      req.adr <= tcb.req.adr;
      req.siz <= tcb.req.siz;
      req.ben <= tcb.req.ben;
      req.wdt <= tcb.req.wdt;
    endtask: transfer_req_lsn

    // transfer response driver
    task automatic transfer_rsp_drv (
      input  transfer_response_t rsp
    );
      // response
      tcb.rsp.rdt <= rsp.rdt;
      tcb.rsp.sts <= rsp.sts;
      // wait for response
      do begin
        @(posedge tcb.clk);
      end while (~tcb.dly[tcb.PHY.DLY].ena);
    endtask: transfer_rsp_drv

  //////////////////////////////////////////////////////////////////////////////
  // transaction sequence non-blocking API
  //////////////////////////////////////////////////////////////////////////////

    // BUG: at DLY=0, there is a race condition between

    // request/response
    task automatic transfer_sequencer (
      ref transfer_array_t transfer_array
    );
      fork
        begin: fork_req
          foreach (transfer_array[i]) begin
            case (DIR)
              "MAN": transfer_req_drv(transfer_array[i].req, transfer_array[i].idl, transfer_array[i].bpr);
              "MON": transfer_req_lsn(transfer_array[i].req, transfer_array[i].idl, transfer_array[i].bpr);
              "SUB": transfer_req_lsn(transfer_array[i].req, transfer_array[i].idl, transfer_array[i].bpr);
            endcase
          end
        end: fork_req
        begin: fork_rsp
          foreach (transfer_array[i]) begin
            case (DIR)
              "MAN": transfer_rsp_lsn(transfer_array[i].rsp);
              "MON": transfer_rsp_lsn(transfer_array[i].rsp);
              "SUB": transfer_rsp_drv(transfer_array[i].rsp);
            endcase
          end
        end: fork_rsp
      join
    endtask: transfer_sequencer

  endclass: tcb_vip_transfer_c

endpackage: tcb_vip_transfer_pkg
