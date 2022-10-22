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
////////////////////////////////////////////////////////////////////////////////

module tcb_sub
  import tcb_pkg::*;
#(
  // response delay
  int unsigned DLY = 1
)(
  // system bus
  tcb_if.sub bus
);

generate
if (DLY != bus.DLY)  $error("%m parameter DLY validation failed");
endgenerate

////////////////////////////////////////////////////////////////////////////////
// request/response queues
////////////////////////////////////////////////////////////////////////////////

  // queues
  tcb_req_t req_que [$];  // request  queue
  tcb_rsp_t rsp_que [$];  // response queue

  // push a response into the queue
  function void rsp (
    input tcb_rsp_t rsp
  );
    rsp_que.push_back(rsp);
  endfunction: rsp

  // pop a request from the queue
  function tcb_req_t req ();
    req = req_que.pop_front();
  endfunction: req

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

  // response pipeline
  tcb_rsp_t rsp_dly [0:DLY-1];

  // initialization before the first clock edge
  initial bus.rdy <= 1'b0;

  // valid/ready handshake and queue
  always @(posedge bus.clk, posedge bus.rst)
  if (bus.rst) begin
    cyc <= 0;
    cnt <= 0;
  end else begin
    // pop response from queue
    if (~cyc | bus.trn) begin
      if (rsp_que.size() > 0) begin
        rsp_tmp = rsp_que.pop_front();
        cyc <= 1'b1;
      end else begin
        cyc <= 1'b0;
      end
    end
    // cycle length counter
//  if (cyc) begin
    if (cyc & bus.vld) begin
      if (bus.trn)  cnt <= 0;
      else          cnt <= cnt + 1;
    end
    // push request into queue
    if (bus.trn) begin
      req_que.push_back(req_tmp);
    end
  end

  // other bus signals
  always_comb
  begin
    // handshake
    bus.rdy = cyc & (cnt >= rsp_tmp.len);
    // cycle length
    req_tmp.len = cnt;
    // request
    req_tmp.wen = bus.wen;
    req_tmp.adr = bus.adr;
    req_tmp.ben = bus.ben;
    req_tmp.wdt = bus.wdt;
    // response
    bus.rdt = rsp_dly[DLY-1].rdt;
    bus.err = rsp_dly[DLY-1].err;
  end

  // TODO
  // response pipeline
  always @(posedge bus.clk)
  rsp_dly[0] <= bus.trn ? rsp_tmp : 'x;
//  for (int unsigned i=0; i<DLY; i++) begin
//  end

endmodule: tcb_sub