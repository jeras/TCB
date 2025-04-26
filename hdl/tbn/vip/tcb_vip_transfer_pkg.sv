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
    parameter  type tcb_rsp_sts_t = tcb_rsp_sts_def_t,
    // debugging options
    parameter  bit  DEBUG = 1'b1
  );

  //////////////////////////////////////////////////////////////////////////////
  // local parameters
  //////////////////////////////////////////////////////////////////////////////

    // byte enable width (number of units inside data)
    localparam int unsigned PHY_BEN = PHY.DAT / PHY.UNT;

    // maximum transfer size
    localparam int unsigned PHY_MAX = $clog2(PHY_BEN);

    // logarithmic transfer size width
    localparam int unsigned PHY_SIZ = $clog2(PHY_MAX+1);

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
          // there is no initialization for a monitor
        end
        // subordinate
        "SUB": begin
          // initialize to idle state
          tcb.rdy = 1'b0;
        end
      endcase
      // start endless delay loop in a background process
      fork
        transfer_dly();
      join_none
    endfunction: new

  //////////////////////////////////////////////////////////////////////////////
  // local types, constants, functions
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
      // transfer ID
      string              id;
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
      bpr: 0,
      // transfer ID
      id: ""
    };

    // transfer equivalence check
    static function automatic logic transfer_check (
      // transfer_array
      input  transfer_t trn_tst,  // test
      input  transfer_t trn_ref,  // reference
      input  transfer_t trn_msk   // mask
    );
      // TODO
      //transfer_check = (trn_tst ==? (trn_ref ~^ trn_msk));
      transfer_check = 1'bx;
    endfunction: transfer_check

    // response delay line
    transfer_response_t rsp_dly [0:PHY.DLY];

  //////////////////////////////////////////////////////////////////////////////
  // transfer manager/subordinate handshake
  //////////////////////////////////////////////////////////////////////////////

    // manager handshake driver
    task automatic transfer_man_drv (
      ref transfer_t itm  // transfer item
    );
      if (DEBUG)  $display("DEBUG: %t: transfer_man_drv begin ID = \"%s\".", $realtime, itm.id);
      // request timing
      repeat (itm.idl) @(posedge tcb.clk);
      // drive transfer
      // handshake
      tcb.vld <= 1'b1;
      // request
      tcb.req.cmd <= itm.req.cmd;
      tcb.req.wen <= itm.req.wen;
      tcb.req.ndn <= itm.req.ndn;
      tcb.req.adr <= itm.req.adr;
      tcb.req.siz <= itm.req.siz;
      tcb.req.ben <= itm.req.ben;
      tcb.req.wdt <= itm.req.wdt;
      // backpressure
      itm.bpr = 0;
      do begin
        @(posedge tcb.clk);
        if (~tcb.rdy) itm.bpr++;
      end while (~tcb.trn);
      // handshake
      tcb.vld <= 1'b0;
      // drive request
      tcb.req.cmd <= 'x;
      tcb.req.wen <= 'x;
      tcb.req.ndn <= 'x;
      tcb.req.adr <= 'x;
      tcb.req.siz <= 'x;
      tcb.req.ben <= 'x;
      tcb.req.wdt <= 'x;
      if (DEBUG)  $display("DEBUG: %t: transfer_man_drv end ID = \"%s\".", $realtime, itm.id);
    endtask: transfer_man_drv

    // subordinate handshake driver
    task automatic transfer_sub_drv (
      ref transfer_t itm  // transfer item
    );
      if (DEBUG)  $display("DEBUG: %t: transfer_sub_drv begin ID = \"%s\".", $realtime, itm.id);
      tcb.rdy <= 1'b0;
      // TODO: rethink this if/else
      itm.idl = 0;
      // request
      if (itm.bpr == 0) begin
        // ready
        tcb.rdy <= 1'b1;
        // wait for transfer
        do begin
          @(posedge tcb.clk);
          if (~tcb.vld) itm.idl++;
        end while (~tcb.trn);
      end else begin
        // backpressure
        for (int unsigned i=0; i<itm.bpr; i+=(tcb.vld?1:0)) begin
          @(posedge tcb.clk);
          if (~tcb.vld) itm.idl++;
        end
        // ready
        tcb.rdy <= 1'b1;
        // wait for transfer
        do begin
          @(posedge tcb.clk);
        end while (~tcb.trn);
      end
      // handshake
      tcb.rdy <= 1'b0;
      // sample request
      itm.req.cmd = tcb.req.cmd;
      itm.req.wen = tcb.req.wen;
      itm.req.ndn = tcb.req.ndn;
      itm.req.adr = tcb.req.adr;
      itm.req.siz = tcb.req.siz;
      itm.req.ben = tcb.req.ben;
      itm.req.wdt = tcb.req.wdt;
      if (DEBUG)  $display("DEBUG: %t: transfer_sub_drv end ID = \"%s\".", $realtime, itm.id);
    endtask: transfer_sub_drv

    // monitor handshake listener
    task automatic transfer_mon_lsn (
      ref transfer_t itm  // transfer item
    );
      if (DEBUG)  $display("DEBUG: %t: transfer_mon_lsn begin ID = \"%s\".", $realtime, itm.id);
      // count idle/backpressure cycles
      itm.idl = 0;
      itm.bpr = 0;
      do begin
        @(posedge tcb.clk);
        if (~tcb.vld           ) itm.idl++;
        if ( tcb.vld & ~tcb.rdy) itm.bpr++;
      end while (~tcb.trn);
      // sample request
      itm.req.cmd = tcb.req.cmd;
      itm.req.wen = tcb.req.wen;
      itm.req.ndn = tcb.req.ndn;
      itm.req.adr = tcb.req.adr;
      itm.req.siz = tcb.req.siz;
      itm.req.ben = tcb.req.ben;
      itm.req.wdt = tcb.req.wdt;
      if (DEBUG)  $display("DEBUG: %t: transfer_mon_lsn end ID = \"%s\".", $realtime, itm.id);
    endtask: transfer_mon_lsn

  //////////////////////////////////////////////////////////////////////////////
  // transfer manager/subordinate response delay line
  //////////////////////////////////////////////////////////////////////////////

    task static transfer_dly;
      if (tcb.PHY.DLY > 0) begin
        forever @(posedge tcb.clk)
        begin
          rsp_dly [1:PHY.DLY] <= rsp_dly [0:PHY.DLY-1];
        end
      end
    endtask: transfer_dly

    // manager delay line (listen to response)
    task automatic transfer_man_dly (
      ref transfer_t itm
    );
      if (DEBUG)  $display("DEBUG: %t: transfer_man_dly begin ID = \"%s\".", $realtime, itm.id);
      if (tcb.PHY.DLY == 0) begin
        // wait for transfer, and sample inside the transfer cycle
        do begin
          @(posedge tcb.clk);
          // sample response
          itm.rsp.rdt = tcb.rsp.rdt;
          itm.rsp.sts = tcb.rsp.sts;
        end while (~tcb.trn);
      end else begin
        // wait for transfer, and sample DLY cycles later
        do begin
          @(posedge tcb.clk);
        end while (~tcb.trn);
        // delay
        repeat (tcb.PHY.DLY) @(posedge tcb.clk);
        // sample response
        itm.rsp.rdt = tcb.rsp.rdt;
        itm.rsp.sts = tcb.rsp.sts;
      end
      if (DEBUG)  $display("DEBUG: %t: transfer_man_dly end ID = \"%s\".", $realtime, itm.id);
    endtask: transfer_man_dly

    // subordinate delay line (drive the response)
    task automatic transfer_sub_dly (
      ref transfer_t itm
    );
      if (DEBUG)  $display("DEBUG: %t: transfer_sub_dly begin ID = \"%s\".", $realtime, itm.id);
      if (tcb.PHY.DLY == 0) begin
        // drive response immediately
        tcb.rsp.rdt = itm.rsp.rdt;
        tcb.rsp.sts = itm.rsp.sts;
        // wait for transfer before exiting task
        do begin
          @(posedge tcb.clk);
        end while (~tcb.trn);
      end else begin
        // wait for transfer
        do begin
          @(posedge tcb.clk);
        end while (~tcb.trn);
        // delay
        repeat (tcb.PHY.DLY-1) @(posedge tcb.clk);
        // drive response
        tcb.rsp.rdt <= itm.rsp.rdt;
        tcb.rsp.sts <= itm.rsp.sts;
        @(posedge tcb.clk);
      end
      if (DEBUG)  $display("DEBUG: %t: transfer_sub_dly end ID = \"%s\".", $realtime, itm.id);
    endtask: transfer_sub_dly

  //////////////////////////////////////////////////////////////////////////////
  // transfer sequence non-blocking API
  //////////////////////////////////////////////////////////////////////////////

    // Questa does not allow the use of `ref` ports in combination with fork-join

    // request/response
    task automatic transfer_sequencer (
      inout transfer_array_t transfer_array
    );
      foreach (transfer_array[i]) begin
        case (DIR)
          "MAN": begin
            fork transfer_man_dly(transfer_array[i]); join_none
                 transfer_man_drv(transfer_array[i]);
          end
          "MON": begin
            fork transfer_man_dly(transfer_array[i]); join_none  // there is no dedicated monitor listener
                 transfer_mon_lsn(transfer_array[i]);
          end
          "SUB": begin
            fork transfer_sub_dly(transfer_array[i]); join_none
                 transfer_sub_drv(transfer_array[i]);
          end
        endcase
      end
      if (DEBUG)  $display("DEBUG: %t: transfer_sequencer end of drivers.", $realtime);
      wait fork;
      if (DEBUG)  $display("DEBUG: %t: transfer_sequencer end of all forks.", $realtime);
    endtask: transfer_sequencer

  endclass: tcb_vip_transfer_c

endpackage: tcb_vip_transfer_pkg
