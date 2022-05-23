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
  tcb_req_t que_req [$];  // request  queue
  tcb_rsp_t que_rsp [$];  // response queue

  // task for pushing a new response into the queue
  task rsp_trn (
    input tcb_rsp_t rsp
  );
    que_rsp.push_back(rsp);
  endtask: rsp_trn

  // temporary structures
  tcb_req_t req;  // request  structure
  tcb_rsp_t rsp;  // response structure

  // response delay queue
  logic [(DLY>0 ? DLY : 1)-1:0] que_trn;

  logic cyc = 1'b0;

  always @(posedge bus.clk, posedge bus.rst)
  if (bus.rst) begin
    rsp.len <=  'd0;
    bus.rdy <= 1'b1;
  end else begin
    if ((~cyc | bus.trn) && que_req.size()) begin
      rsp = que_rsp.pop_front();
      cyc = 1'b1;
    end
    // request
    if (bus.vld && req.len) begin
      req.len <= req.len - 1;
    end
    if (req.len) begin
      req.len <= req.len - 1;
    end
    if (bus.trn) begin
      req.wen <= bus.wen;
      req.adr <= bus.adr;
      req.ben <= bus.ben;
      req.wdt <= bus.wdt;
      que_req.push_back(req);
    end
    // response
    if (bus.trn) begin
      bus.rdt <= rsp.rdt;
      bus.err <= rsp.err;
    end
  end

endmodule: tcb_sub