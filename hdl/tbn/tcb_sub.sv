////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus subordinate
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

module tcb_sub
  import tcb_pkg::*;
#(
  // response delay
  int unsigned DLY = 1
)(
  // system bus
  tcb_if.sub bus
);

  // queues are initialized outside this module
  tcb_req_t req_que [$];  // request  queue
  tcb_rsp_t rsp_que [$];  // response queue
  // cycle length counters
  int unsigned rsp_cnt;

  // task for pushing a new response into the queue
  task rsp_trn (
    input tcb_rsp_t rsp
  );
    rsp_que.push_back(rsp);
  endtask: rsp_trn

  // temporary structures
  tcb_req_t req;  // request  structure

  // initialization before the first clock edge
  initial bus.rdy <= 1'b0;

  // NOTE: the READY signal is usually driven asynchronously

  // valid/ready handshake and queue
  always @(posedge bus.clk, posedge bus.rst)
  if (bus.rst) begin
    bus.rdy <= 1'b0;
    rsp_cnt <=  'd0;
  end else begin
    // ready timer
    if (bus.vld) begin
      if (bus.rdy) begin
        rsp_cnt <= 0;
      end else begin
        rsp_cnt <= rsp_cnt + 1;
      end
    end
    // push request into queue
    if (bus.trn) begin
      req_que.push_back(req);
    end
    // pop response from queue
    if (bus.rsp && rsp_que.size()) begin
      void'(rsp_que.pop_front());
    end
  end

  // handshake
  always_comb
  begin
    if (rsp_que.size()) begin
      if (rsp_cnt < rsp_que[0].len) begin
        bus.rdy <= 1'b0;
      end else begin
        bus.rdy <= 1'b1;
      end
    end else begin
      bus.rdy <= 1'b0;
    end
  end

  // other bus signals
  always_comb
  begin
    // request
    req.wen = bus.wen;
    req.adr = bus.adr;
    req.ben = bus.ben;
    req.wdt = bus.wdt;
    // response
    if (bus.rsp && rsp_que.size()) begin
      bus.rdt = rsp_que[0].rdt;
      bus.err = rsp_que[0].err;
    end else begin
      bus.rdt = 'x;
      bus.err = 'x;
    end
  end

endmodule: tcb_sub