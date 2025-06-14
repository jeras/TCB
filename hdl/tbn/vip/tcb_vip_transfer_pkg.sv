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
    // configuration parameters
    parameter  type cfg_t = tcb_cfg_t,   // configuration parameter type
    parameter  cfg_t CFG = TCB_CFG_DEF,  // configuration parameter
    // request/response structure types
    parameter  type req_t = tcb_req_t,   // request
    parameter  type rsp_t = tcb_rsp_t,   // response
    // VIP (not to be used in RTL)
    parameter  type vip_t = tcb_vip_t,   // VIP parameter type
    parameter  vip_t VIP = TCB_VIP_DEF,  // VIP parameter
    // debugging options
    parameter  bit  DEBUG = 1'b0
  );

  //////////////////////////////////////////////////////////////////////////////
  // virtual interface
  //////////////////////////////////////////////////////////////////////////////

    // virtual interface type definition
    typedef virtual tcb_if #(
      .cfg_t (cfg_t),
      .CFG   (CFG),
      .req_t (req_t),
      .rsp_t (rsp_t),
      .vip_t (vip_t),
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

  //////////////////////////////////////////////////////////////////////////////
  // transfer manager/subordinate/monitor handshake
  //////////////////////////////////////////////////////////////////////////////

    // manager handshake driver
    task automatic handshake_manager (
      ref transfer_t itm  // transfer item
    );
      int unsigned itm_idl;
      if (DEBUG)  $info("DEBUG: %t: handshake_manager begin ID = \"%s\".", $realtime, itm.id);
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
      if (DEBUG)  $info("DEBUG: %t: handshake_manager end ID = \"%s\".", $realtime, itm.id);
    endtask: handshake_manager

    // subordinate handshake driver
    task automatic handshake_subordinate (
      ref transfer_t itm  // transfer item
    );
      int unsigned itm_bpr;
      if (DEBUG)  $info("DEBUG: %t: handshake_subordinate begin ID = \"%s\".", $realtime, itm.id);
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
      if (DEBUG)  $info("DEBUG: %t: handshake_subordinate end ID = \"%s\".", $realtime, itm.id);
    endtask: handshake_subordinate

    // monitor handshake listener
    task automatic handshake_monitor (
      ref transfer_t itm  // transfer item
    );
      if (DEBUG)  $info("DEBUG: %t: handshake_monitor begin ID = \"%s\".", $realtime, itm.id);
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
      if (DEBUG)  $info("DEBUG: %t: handshake_monitor end ID = \"%s\".", $realtime, itm.id);
    endtask: handshake_monitor

  //////////////////////////////////////////////////////////////////////////////
  // transfer manager/subordinate/monitor response delay line
  //////////////////////////////////////////////////////////////////////////////

    // monitor delay line (listen to response)
    task automatic handshake_delay (
      ref transfer_t itm
    );
      if (DEBUG)  $info("DEBUG: %t: handshake_delay begin ID = \"%s\".", $realtime, itm.id);
      // wait for transfer
      do begin
        @(posedge tcb.clk);
      end while (~tcb.trn);
      // delay
      repeat (tcb.CFG.HSK.DLY) @(posedge tcb.clk);
      // sample response
      itm.rsp = tcb.rsp;
      if (DEBUG)  $info("DEBUG: %t: handshake_delay end ID = \"%s\".", $realtime, itm.id);
    endtask: handshake_delay

  //////////////////////////////////////////////////////////////////////////////
  // transfer sequence (non-blocking)
  //////////////////////////////////////////////////////////////////////////////

    // request/response
    task automatic transfer_sequencer (
      // use of `ref` ports in combination with fork-join is not allowed
      inout transfer_array_t transfer_array
    );
      foreach (transfer_array[i]) begin
        case (DIR)
          "MAN": begin
            fork handshake_delay      (transfer_array[i]); join_none
                 handshake_manager    (transfer_array[i]);
          end
          "MON": begin
            fork handshake_delay      (transfer_array[i]); join_none
                 handshake_monitor    (transfer_array[i]);
          end
          "SUB": begin
            fork handshake_delay      (transfer_array[i]); join_none
                 handshake_subordinate(transfer_array[i]);
          end
        endcase
      end
      if (DEBUG)  $info("DEBUG: %t: transfer_sequencer end of drivers.", $realtime);
      wait fork;
      if (DEBUG)  $info("DEBUG: %t: transfer_sequencer end of all forks.", $realtime);
    endtask: transfer_sequencer

  //////////////////////////////////////////////////////////////////////////////
  // transfer monitor
  //////////////////////////////////////////////////////////////////////////////

    // monitor delayed request/response
    task automatic transfer_monitor (
      ref transfer_queue_t transfer_queue
    );
      if (DEBUG)  $info("DEBUG: %t: transfer_monitor started.", $realtime);
      forever
      begin: loop
        // wait for delayed transfer
        do begin
          @(posedge tcb.clk);
        end while (~tcb.trn_dly[tcb.CFG.HSK.DLY]);
        // sample delayed request and response
        transfer_queue.push_back('{req: tcb.req_dly[tcb.CFG.HSK.DLY], rsp: tcb.rsp, default: 'x});
      end: loop
      if (DEBUG)  $info("DEBUG: %t: transfer_monitor stopped.", $realtime);
    endtask: transfer_monitor

  endclass: tcb_vip_transfer_c

endpackage: tcb_vip_transfer_pkg
