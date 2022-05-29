////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus manager
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
///////////////////////////////////////////////////////////////////////////////

module tcb_man
  import tcb_pkg::*;
#(
  // response delay
  int unsigned DLY = 1
)(
  // system bus
  tcb_if.man bus
);

  // queues
  tcb_req_t req_que [$];  // request  queue
  tcb_rsp_t rsp_que [$];  // response queue
  // cycle length counters
  int unsigned req_cnt;

  // task for pushing a new request into the queue
  task req_trn (
    input tcb_req_t req
  );
    req_que.push_back(req);
  endtask: req_trn

  // temporary structures
  tcb_rsp_t rsp;  // response structure

  // initialization before the first clock edge
  initial bus.vld <= 1'b0;

  // NOTE: the VALID signal is usually driven synchronously

  // valid/ready handshake and queue
  always @(posedge bus.clk, posedge bus.rst)
  if (bus.rst) begin
    bus.vld <= 1'b0;
    req_cnt <=  'd0;
  end else begin
    // handshake
    if (req_que.size() > int'(bus.trn)) begin
      if (req_cnt < req_que[0].len) begin
        req_cnt <= req_cnt + 1;
        bus.vld <= 1'b0;
      end else begin
        if (bus.trn) begin
          req_cnt <=  'd0;
        end
        bus.vld <= 1'b1;
      end
    end else begin
      bus.vld <= 1'b0;
    end
    // pop request from queue
    if (bus.trn && req_que.size()) begin
      void'(req_que.pop_front());
    end
    // push response into queue
    if (bus.rsp) begin
      $display("DEBUG: readback %d", rsp_que.size());
      rsp_que.push_back(rsp);
      $display("DEBUG: readback %d", rsp_que.size());
    end
  end

  // other bus signals
  always_comb
  begin
    // request
    if (bus.vld && rsp_que.size()) begin
      bus.wen = req_que[0].wen;
      bus.adr = req_que[0].adr;
      bus.ben = req_que[0].ben;
      bus.wdt = req_que[0].wdt;
    end else begin
      bus.wen = 'x;
      bus.adr = 'x;
      bus.ben = 'x;
      bus.wdt = 'x;
    end
    // response
    rsp.rdt = bus.rdt;
    rsp.err = bus.err;
  end

endmodule: tcb_man