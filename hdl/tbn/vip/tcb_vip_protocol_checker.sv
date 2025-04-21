////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) protocol checker
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

module tcb_vip_protocol_checker (
  // TCB interface
  tcb_if.mon tcb
);

  import tcb_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// local signals
////////////////////////////////////////////////////////////////////////////////

  // TCB system bus delayed by DLY clock periods
  tcb_if #(.PHY (tcb.PHY)) dly (.clk (tcb.clk), .rst (tcb.rst));

////////////////////////////////////////////////////////////////////////////////
// protocol monitor
////////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge tcb.clk)
  if ($realtime > 0) begin
    // valid/ready known
    assert (!$isunknown(tcb.vld)) else $fatal(0, "TCB %m: tcb.vld is unknown.");
    // TODO: reconsider whether ready must always be known
    assert (!$isunknown(tcb.rdy)) else $fatal(0, "TCB %m: tcb.rdy is unknown.");
    // reset state
    if (tcb.rst) begin
      assert(~tcb.vld) else $fatal(0, "TCB %m: valid must be low during reset.");
    end
    // reset sequence
    if ($fell(tcb.rst)) begin
      assert(~tcb.vld) else $fatal(0, "TCB %m: valid must be low during first cycle after reset release.");
    end
    // operation
    if (~tcb.rst) begin
      // while valid
      if (tcb.vld == 1'b1) begin
        // ready known
        assert (!$isunknown(tcb.rdy)) else $fatal(0, "TCB %m: tcb.rdy is unknown during a valid cycle.");
        // write enable defined/driven     
        assert (!$isunknown(tcb.req.wen)) else $fatal(0, "TCB %m: tcb.req.wen is unknown during a cycle.");
        case (tcb.PHY.MOD)
          TCB_LOG_SIZE: assert (!$isunknown(tcb.req.siz)) else $fatal(0, "TCB %m: tcb.req.siz is unknown during a cycle.");
          TCB_BYTE_ENA: assert (!$isunknown(tcb.req.ben)) else $fatal(0, "TCB %m: tcb.req.ben is unknown during a cycle.");
        endcase
        // TODO: check other signals too
      end
      // while stalling
      if (tcb.stl) begin
        assert ($stable(tcb.req)) else $fatal(0, "TCB %m: tcb.req is unstable during a stall.");
      end
      // read data hold (DLY>1)
      // TODO
    end
  end

endmodule: tcb_vip_protocol_checker
