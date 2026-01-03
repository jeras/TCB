////////////////////////////////////////////////////////////////////////////////
// TCB lite (Tightly Coupled Bus) VIP (Verification IP) transfer PacKaGe
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
        parameter int unsigned DELAY =  1,  // response delay
        parameter int unsigned WIDTH = 32,  // data/address width (only 32/64 are supported)
        parameter bit [WIDTH-1] MASK = '1,  // address mask
        parameter bit           MODE = '1   // bus mode (0-logarithmic size, 1-byte enable)
        // debugging options
        parameter  bit  DEBUG = 1'b0
    );

    ///////////////////////////////////////
    // virtual interface
    ///////////////////////////////////////

        // virtual interface type definition
        typedef virtual tcb_lite_if #(
            .DELAY (DELAY),
            .WIDTH (WIDTH),
            .MASK  (MASK ),
            .MODE  (MODE ),
            .VIP   (VIP  )
        ) tcb_vif_t;

        // virtual interface instance
        tcb_vif_t tcb;

        // direction
        string DIR = "";

        //constructor
        function new (
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

    ///////////////////////////////////////
    // local types, constants, functions
    ///////////////////////////////////////

        // TCB transfer structure
        typedef struct {
            // request
            logic               lck;  // arbitration lock
            logic               wen;  // write enable (0-read, 1-write)
            logic [WIDTH  -1:0] adr;  // address
            logic [      2-1:0] siz;  // transfer size
            logic [WIDTH/8-1:0] byt;  // byte enable
            logic [WIDTH  -1:0] wdt;  // write data
            // response
            logic [WIDTH  -1:0] rdt;  // read data
            logic               err;  // bus error
            // timing idle/backpressure
            int unsigned idl;  // idle
            int unsigned bpr;  // backpressure
            // transfer ID
            string       id;
        } transfer_t;

        typedef transfer_t transfer_array_t [];
        typedef transfer_t transfer_queue_t [$];

    ///////////////////////////////////////
    // transfer manager/subordinate/monitor handshake
    ///////////////////////////////////////

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
                    // start handshake
                    tcb.vld <= 1'b1;
                    // request
                    tcb.lck <= itm.lck;
                    tcb.wen <= itm.wen;
                    tcb.adr <= itm.adr;
                    tcb.siz <= itm.siz;
                    tcb.byt <= itm.byt;
                    tcb.wdt <= itm.wdt;
                end
                @(posedge tcb.clk);
                if (~tcb.vld) itm_idl++;
                if (~tcb.rdy) itm.bpr++;
            end while (~tcb.trn);
            // end handshake
            tcb.vld <= 1'b0;
            // request
            tcb.lck <= 'x;
            tcb.wen <= 'x;
            tcb.adr <= 'x;
            tcb.siz <= 'x;
            tcb.byt <= 'x;
            tcb.wdt <= 'x;
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
                    // start handshake
                    tcb.rdy <= 1'b1;
                    // response
                    tcb.rdt_dly[0] <= itm.rdt;
                    tcb.err_dly[0] <= itm.err;
                end
                @(posedge tcb.clk);
                if (~tcb.vld) itm.idl++;
                if (~tcb.rdy) itm_bpr++;
            end while (~tcb.trn);
            // end handshake
            tcb.rdy <= 1'b0;
            // response
            tcb.rdt_dly[0] <= 'x;
            tcb.err_dly[0] <= 'x;
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
            // sample request  // TODO: operator <= ?
            itm.lck = tcb.lck;
            itm.wen = tcb.wen;
            itm.adr = tcb.adr;
            itm.siz = tcb.siz;
            itm.byt = tcb.byt;
            itm.wdt = tcb.wdt;
            if (DEBUG)  $info("DEBUG: %t: handshake_monitor end ID = \"%s\".", $realtime, itm.id);
        endtask: handshake_monitor

    ///////////////////////////////////////
    // transfer manager/subordinate/monitor response delay line
    ///////////////////////////////////////

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
            repeat (tcb.DELAY) @(posedge tcb.clk);
            // sample response  // TODO: operator <= ?
            itm.rdt = tcb.rdt;
            itm.err = tcb.err;
            if (DEBUG)  $info("DEBUG: %t: handshake_delay end ID = \"%s\".", $realtime, itm.id);
        endtask: handshake_delay

    ///////////////////////////////////////
    // transfer sequence (non-blocking)
    ///////////////////////////////////////

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

    ///////////////////////////////////////
    // transfer monitor
    ///////////////////////////////////////

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
                end while (~tcb.trn_dly[tcb.DELAY]);
                // sample delayed request and response
                transfer_queue.push_back('{req: tcb.req_dly[tcb.DELAY], rsp: tcb.rsp, default: 'x});
            end: loop
            if (DEBUG)  $info("DEBUG: %t: transfer_monitor stopped.", $realtime);
        endtask: transfer_monitor

    endclass: tcb_vip_transfer_c

endpackage: tcb_vip_transfer_pkg
