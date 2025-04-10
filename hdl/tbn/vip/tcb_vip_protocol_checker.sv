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
// delay TCB signals
////////////////////////////////////////////////////////////////////////////////

  // delayed signals
  always_ff @(posedge tcb.clk, posedge tcb.rst)
  if (tcb.rst) begin
    // TCB
    dly.vld <= '0;
    dly.req <= '{default: 'x};
    dly.rsp <= '{default: 'x};
    dly.rdy <= '1;
  end else begin
    // TCB
    dly.vld <= tcb.vld;
    dly.req <= tcb.req;
    dly.rsp <= tcb.rsp;
    dly.rdy <= tcb.rdy;
  end

// TODO: add checking whether data is unchanging while valid

////////////////////////////////////////////////////////////////////////////////
// protocol monitor
////////////////////////////////////////////////////////////////////////////////


  // used to skip first clock posedge at time 0
  logic protocol_check = 1'b0;

  always_ff @(posedge tcb.clk)
  begin
    // skip first clock posedge at time 0
    protocol_check <= 1'b1;
    if (protocol_check) begin
      // VALID must always be defined
      assert ((tcb.vld !== 1'bx) && (tcb.vld !== 1'bz)) else $fatal("TCB: tcb.vld is undefined.");
      // if VALID is active other request signal must also be defined
      if (tcb.vld == 1'b1) begin
        assert (( tcb.rdy     !== 1'bx) && ( tcb.rdy     !== 1'bz)) else $fatal("TCB: tcb.rdy is undefined during a cycle.");
        assert (( tcb.req.wen !== 1'bx) && ( tcb.req.wen !== 1'bz)) else $fatal("TCB: tcb.req.wen is undefined during a cycle.");
        case (tcb.PHY.MOD)

          TCB_RISC_V:
          begin
            assert (^tcb.req.siz !== 1'bx) else $fatal("TCB: tcb.req.siz is undefined during a cycle.");
          end

          TCB_MEMORY:
          begin
            assert (^tcb.req.ben !== 1'bx) else $fatal("TCB: tcb.req.ben is undefined during a cycle.");
          end

          default:
          begin
          end
        endcase
        // TODO: check other signals too
      end
    end
  end

endmodule: tcb_vip_protocol_checker
