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
    // handshake parameter
    parameter  int unsigned DLY = TCB_DLY_DEF,    // response delay
    // PHY parameters (combined into a structure)
    parameter  type phy_t = tcb_phy_t,  // PHY parameter type
    parameter  phy_t PHY = TCB_PHY_DEF,
    // request/response structure types
    parameter  type req_t = tcb_req_t,  // request
    parameter  type rsp_t = tcb_rsp_t,  // response
    // VIP (not to be used in RTL)
    parameter  bit  VIP = 0, // VIP end node
    // debugging options
    parameter  bit  DEBUG = 1'b0
  );

  //////////////////////////////////////////////////////////////////////////////
  // virtual interface
  //////////////////////////////////////////////////////////////////////////////

    // virtual interface type definition
    typedef virtual tcb_if #(
      .DLY   (DLY),
      .phy_t (phy_t),
      .PHY   (PHY),
      .req_t (req_t),
      .rsp_t (rsp_t),
      .VIP   (VIP)
    ) tcb_vif_t;

    // virtual interface instance
    tcb_vif_t tcb;

    // direction
    string DIR = "";

    //constructor
    function new(
      tcb_vif_t tcb,
      string DIR = "MON"
    );
      this.tcb = tcb;
      this.DIR = DIR;
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
        default: $fatal(0, "Unsupported DIR value: \"%s\"", DIR);
      endcase
    endfunction: new

  //////////////////////////////////////////////////////////////////////////////
  // local types, constants, functions
  //////////////////////////////////////////////////////////////////////////////

    // TCB transfer structure
    typedef struct {
      // request/response
      req_t req;  // request
      rsp_t rsp;  // response
      // timing idle/backpressure
      int unsigned idl;  // idle
      int unsigned bpr;  // backpressure
      // transfer ID
      string       id;
    } transfer_t;

    typedef transfer_t transfer_array_t [];
    typedef transfer_t transfer_queue_t [$];

    // constants
    static const transfer_t TRANSFER_INIT = '{
      req: '{default: 'x},  // request
      rsp: '{default: 'x},  // response
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

  //////////////////////////////////////////////////////////////////////////////
  // transfer manager/subordinate handshake
  //////////////////////////////////////////////////////////////////////////////

    // manager handshake driver
    task automatic transfer_man_drv (
      ref transfer_t itm  // transfer item
    );
      int unsigned itm_idl;
      if (DEBUG)  $display("DEBUG: %t: transfer_man_drv begin ID = \"%s\".", $realtime, itm.id);
      // initialize timing counters
      itm_idl = 0;
      itm.bpr = 0;
      // drive transfer
      tcb.vld <= 1'b0;
      do begin
        if (itm_idl == itm.idl) begin
          // start handshake and request
          tcb.vld <= 1'b1;
          tcb.req <= itm.req;
        end
        @(posedge tcb.clk);
        if (~tcb.vld) itm_idl++;
        if (~tcb.rdy) itm.bpr++;
      end while (~tcb.trn);
      // end handshake and request
      tcb.vld <= 1'b0;
      tcb.req <= '{default: 'x};
      if (DEBUG)  $display("DEBUG: %t: transfer_man_drv end ID = \"%s\".", $realtime, itm.id);
    endtask: transfer_man_drv

    // subordinate handshake driver
    task automatic transfer_sub_drv (
      ref transfer_t itm  // transfer item
    );
      int unsigned itm_bpr;
      if (DEBUG)  $display("DEBUG: %t: transfer_sub_drv begin ID = \"%s\".", $realtime, itm.id);
      // initialize timing counters
      itm.idl = 0;
      itm_bpr = 0;
      // drive transfer
      tcb.rdy <= 1'b0;
      do begin
        if (itm_bpr == itm.bpr) begin
          // start handshake and response
          tcb.rdy <= 1'b1;
          tcb.rsp_dly[0] <= itm.rsp;
        end
        @(posedge tcb.clk);
        if (~tcb.vld) itm.idl++;
        if (~tcb.rdy) itm_bpr++;
      end while (~tcb.trn);
      // end handshake and response
      tcb.rdy <= 1'b0;
      tcb.rsp_dly[0] <= '{default: '0};
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
        if (~tcb.vld) itm.idl++;
        if (~tcb.rdy) itm.bpr++;
      end while (~tcb.trn);
      // sample request
      itm.req = tcb.req;
      if (DEBUG)  $display("DEBUG: %t: transfer_mon_lsn end ID = \"%s\".", $realtime, itm.id);
    endtask: transfer_mon_lsn

  //////////////////////////////////////////////////////////////////////////////
  // transfer manager/subordinate response delay line
  //////////////////////////////////////////////////////////////////////////////

    // manager delay line (listen to response)
    task automatic transfer_mon_dly (
      ref transfer_t itm
    );
      if (DEBUG)  $display("DEBUG: %t: transfer_mon_dly begin ID = \"%s\".", $realtime, itm.id);
      // wait for transfer
      do begin
        @(posedge tcb.clk);
      end while (~tcb.trn);
      // delay
      repeat (tcb.DLY) @(posedge tcb.clk);
      // sample response
      itm.rsp = tcb.rsp;
      if (DEBUG)  $display("DEBUG: %t: transfer_mon_dly end ID = \"%s\".", $realtime, itm.id);
    endtask: transfer_mon_dly

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
            fork transfer_mon_dly(transfer_array[i]); join_none
                 transfer_man_drv(transfer_array[i]);
          end
          "MON": begin
            fork transfer_mon_dly(transfer_array[i]); join_none
                 transfer_mon_lsn(transfer_array[i]);
          end
          "SUB": begin
//            fork transfer_sub_dly(transfer_array[i]); join_none
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
