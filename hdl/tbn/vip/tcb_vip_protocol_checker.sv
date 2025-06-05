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
// handshake layer
////////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge tcb.clk)
  if ($realtime > 0) begin
    // valid/ready known
    assert (!$isunknown(tcb.vld)) else $error("TCB: tcb.vld is unknown.");
    // reset state
    if (tcb.rst) begin
      assert(~tcb.vld) else $error("TCB: valid must be low during reset.");
    end
    // reset sequence
    if ($fell(tcb.rst)) begin
      assert(~tcb.vld) else $error("TCB: valid must be low during first cycle after reset release.");
    end
    // while valid
    if (tcb.vld == 1'b1) begin
      // ready known
      assert (!$isunknown(tcb.rdy)) else $error("TCB: tcb.rdy is unknown during a valid cycle.");
      // while stalling
      if ($past(tcb.stl)) begin
        assert ($stable(tcb.req)) else $error("TCB: tcb.req is unstable during a stall.");
      end
    end
    // read data hold (HSK.DLY>1)
    // TODO
  end

////////////////////////////////////////////////////////////////////////////////
// bus layer
////////////////////////////////////////////////////////////////////////////////

  // request
  always_ff @(posedge tcb.clk)
  if ($realtime > 0) begin
    // while valid
    if (tcb.vld == 1'b1) begin
      // framing
      if (tcb.CFG.BUS.LCK == TCB_LCK_PRESENT) begin
        assert (!$isunknown(tcb.req.lck)) else $error("TCB: tcb.req.lck is unknown during a transfer cycle.");
      end
      // channel
      if (tcb.CFG.BUS.CHN inside {TCB_CHN_FULL_DUPLEX, TCB_CHN_HALF_DUPLEX}) begin
        assert (!$isunknown(tcb.req.wen)) else $error("TCB: tcb.req.wen is unknown during a transfer cycle.");
      end
      if (tcb.CFG.BUS.CHN inside {TCB_CHN_FULL_DUPLEX}) begin
        assert (!$isunknown(tcb.req.ren)) else $error("TCB: tcb.req.ren is unknown during a transfer cycle.");
      end
      // burst
      if (tcb.CFG.BUS.LEN > 0) begin
        if (tcb.req.ben) begin
          assert (!$isunknown(tcb.req.len)) else $error("TCB: tcb.req.len is unknown during a transfer cycle.");
        end
      end
      // prefetch
      if (tcb.CFG.BUS.PRF == TCB_PRF_PRESENT) begin
        assert (!$isunknown(tcb.req.rpt)) else $error("TCB: tcb.req.rpt is unknown during a transfer cycle.");
        assert (!$isunknown(tcb.req.inc)) else $error("TCB: tcb.req.inc is unknown during a transfer cycle.");
      end
      // address and next address
      assert (!$isunknown(tcb.req.adr[tcb.CFG.BUS.ADR-1:0])) else $error("TCB: tcb.req.adr[tcb.CFG.BUS.ADR-1:0] is unknown during a transfer cycle.");
      if (tcb.CFG.BUS.NXT == TCB_NXT_PRESENT) begin
        assert (!$isunknown(tcb.req.nxt[tcb.CFG.BUS.ADR-1:0])) else $error("TCB: tcb.req.nxt[tcb.CFG.BUS.ADR-1:0] is unknown during a transfer cycle.");
      end
      if (tcb.CFG.BUS.MOD == TCB_MOD_LOG_SIZE) begin
        assert (!$isunknown(tcb.req.siz)) else $error("TCB: tcb.req.siz is unknown during a transfer cycle.");
      end
      if (tcb.CFG.BUS.MOD == TCB_MOD_BYTE_ENA) begin
        assert (!$isunknown(tcb.req.byt)) else $error("TCB: tcb.req.byt is unknown during a transfer cycle.");
      end
      // endianness
      if (tcb.CFG.BUS.NDN == TCB_NDN_BI_NDN) begin
        assert (!$isunknown(tcb.req.ndn)) else $error("TCB: tcb.req.ndn is unknown during a transfer cycle.");
      end
    end
  end

  // request
  always_ff @(posedge tcb.clk)
  if ($realtime > 0) begin
    // request/write data bus
    if (tcb.CFG.BUS.CHN != TCB_CHN_READ_ONLY) begin
      if (tcb.trn) begin
        if (tcb.req.wen | (tcb.CFG.BUS.CHN == TCB_CHN_WRITE_ONLY)) begin
          if (tcb.CFG.BUS.MOD == TCB_MOD_LOG_SIZE) begin
            for (int unsigned i=0; i<2**tcb.req.siz; i++) begin
              assert (!$isunknown(tcb.req.wdt[i])) else $error("TCB: tcb.req.wdt[%0d] is unknown during a transfer cycle.", i);
            end
          end
          if (tcb.CFG.BUS.MOD == TCB_MOD_BYTE_ENA) begin
            for (int unsigned i=0; i<tcb.CFG_BUS_BYT; i++) begin
              if (tcb.req.byt[i]) begin
                assert (!$isunknown(tcb.req.wdt[i])) else $error("TCB: tcb.req.wdt[%0d] is unknown during a transfer cycle.", i);
              end
            end
          end
        end
      end
    end
    // response/read data bus and data sizing
    if (tcb.CFG.BUS.CHN != TCB_CHN_WRITE_ONLY) begin
      if (tcb.trn_dly[tcb.CFG.HSK.DLY]) begin
        if (~tcb.req_dly[tcb.CFG.HSK.DLY].wen | (tcb.CFG.BUS.CHN == TCB_CHN_READ_ONLY)) begin
          if (tcb.CFG.BUS.MOD == TCB_MOD_LOG_SIZE) begin
            for (int unsigned i=0; i<2**tcb.req_dly[tcb.CFG.HSK.DLY].siz; i++) begin
              assert (!$isunknown(tcb.rsp.rdt[i])) else $error("TCB: tcb.rsp.rdt[%0d] is unknown during a transfer cycle.", i);
            end
          end
          if (tcb.CFG.BUS.MOD == TCB_MOD_BYTE_ENA) begin
            for (int unsigned i=0; i<tcb.CFG_BUS_BYT; i++) begin
              if (tcb.req_dly[tcb.CFG.HSK.DLY].byt[i]) begin
                assert (!$isunknown(tcb.rsp.rdt[i])) else $error("TCB: tcb.rsp.rdt[%0d] is unknown during a transfer cycle.", i);
              end
            end
          end
        end
        // response status check
        assert (!$isunknown(tcb.rsp.sts)) else $error("TCB: tcb.rsp.sts is unknown during a transfer cycle.");
      end
    end
  end

////////////////////////////////////////////////////////////////////////////////
// BMA layer
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Transaction framing layer
////////////////////////////////////////////////////////////////////////////////

endmodule: tcb_vip_protocol_checker
