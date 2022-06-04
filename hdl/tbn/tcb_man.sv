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
////////////////////////////////////////////////////////////////////////////////

module tcb_man
  import tcb_pkg::*;
#(
  // response delay
  int unsigned DLY = 1
)(
  // system bus
  tcb_if.man bus
);

generate
if (DLY != bus.DLY)  $error("%m parameter DLY checker failed");
endgenerate

////////////////////////////////////////////////////////////////////////////////
// request/response queues
////////////////////////////////////////////////////////////////////////////////

  // queues
  tcb_req_t req_que [$];  // request  queue
  tcb_rsp_t rsp_que [$];  // response queue

  // push a request into the queue
  function void req (
    input tcb_req_t req
  );
    req_que.push_back(req);
  endfunction: req

  // pop a response from the queue
  function tcb_rsp_t rsp ();
    rsp = rsp_que.pop_front();
  endfunction: rsp

  // debug queue size
  int unsigned req_siz;
  int unsigned rsp_siz;
  always @(posedge bus.clk)
  begin
    req_siz <= req_que.size();
    rsp_siz <= rsp_que.size();
  end

////////////////////////////////////////////////////////////////////////////////
// transfer cycle
////////////////////////////////////////////////////////////////////////////////

  // active cycle
  bit cyc = 1'b0;

  // cycle length counter
  int unsigned cnt;

  // temporary request/response structure
  tcb_req_t req_tmp;
  tcb_rsp_t rsp_tmp;

  // initialization before the first clock edge
  initial bus.vld <= 1'b0;

  // valid/ready handshake and queue
  always @(posedge bus.clk, posedge bus.rst)
  if (bus.rst) begin
    cyc <= 0;
    cnt <= 0;
  end else begin
    // pop request from queue
    if (~cyc | bus.trn) begin
      if (req_que.size()) begin
        req_tmp <= req_que.pop_front();
        cyc <= 1'b1;
      end else begin
        cyc <= 1'b0;
      end
    end
    // cycle length counter
    if (cyc) begin
      if (bus.trn)  cnt <= 0;
      else          cnt <= cnt + 1;
    end
    // push response into queue
    if (bus.rsp) begin
      rsp_que.push_back(rsp_tmp);
    end
  end

  // other bus signals
  always_comb
  begin
    // handshake
    bus.vld = cyc & (cnt >= req_tmp.len);
    // cycle length
    rsp_tmp.len = cnt;  // TODO: delay to DLY
    // request
    bus.wen = bus.vld ? req_tmp.wen : 'x;
    bus.adr = bus.vld ? req_tmp.adr : 'x;
    bus.ben = bus.vld ? req_tmp.ben : 'x;
    bus.wdt = bus.vld ? req_tmp.wdt : 'x;
    // response
    rsp_tmp.rdt = bus.rdt;
    rsp_tmp.err = bus.err;
  end

endmodule: tcb_man