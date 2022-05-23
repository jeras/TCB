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

  // queues are initialized outside this module
  tcb_req_t que_req [$];  // request  queue
  tcb_rsp_t que_rsp [$];  // response queue

  // task for pushing a new request into the queue
  task req_trn (
    input tcb_req_t req
  );
    que_req.push_back(req);
  endtask: req_trn

  // temporary structures
  tcb_req_t req;  // request  structure
  tcb_rsp_t rsp;  // response structure

  // response delay queue
  logic [(DLY>0 ? DLY : 1)-1:0] que_trn;

  always @(posedge bus.clk, posedge bus.rst)
  if (bus.rst) begin
    req.len <=  'd0;
    bus.vld <= 1'b0;
  end else begin
    // request
    if (req.len) begin
      req.len <= req.len - 1;
    end else begin
      if (bus.idl && que_req.size()) begin
        req = que_req.pop_front();
        bus.vld <= 1'b1;
        bus.wen <= req.wen;
        bus.adr <= req.adr;
        bus.ben <= req.ben;
        bus.wdt <= req.wdt;
      end else begin
        bus.vld <= 1'b0;
      end
    end
    // response
    if (que_trn[0]) begin
      rsp.rdt <= bus.rdt;
      rsp.err <= bus.err;
      que_rsp.push_back(rsp);
    end
  end

  // response delay queue
  generate
  if (DLY > 0) begin: gen_dly

    if (DLY == 1) begin: gen_dly_1

      always @(posedge bus.clk, posedge bus.rst)
      if (bus.rst)  que_trn <= '0;
      else          que_trn <= bus.trn;

    end: gen_dly_1
    else begin: gen_dly_1p

      always @(posedge bus.clk, posedge bus.rst)
      if (bus.rst)  que_trn <= '0;
      else          que_trn <= {que_trn[DLY-2:0], bus.trn};

    end: gen_dly_1p

  end: gen_dly
  else begin: gen_dly_0

    assign que_trn = bus.trn;

  end: gen_dly_0
  endgenerate

endmodule: tcb_man