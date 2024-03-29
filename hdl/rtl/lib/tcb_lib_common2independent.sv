////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) library common to independant channel conversion
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

module tcb_lib_common2independent (
  // TCB common subordinate port (manager device connects here)
  tcb_if.sub tcb_cmn_sub,
  // TCB independant manager ports (subordinate device connects here)
  tcb_if.man tcb_rdc_man,
  tcb_if.man tcb_wrc_man
);

////////////////////////////////////////////////////////////////////////////////
// parameter validation
////////////////////////////////////////////////////////////////////////////////

`ifdef ALTERA_RESERVED_QIS
`else
  // camparing subordinate and manager interface parameters
  generate
    if (tcb_cmn_sub.PHY != tcb_wrc_man.PHY)  $error("ERROR: %m parameter (tcb_cmn_sub.PHY = %p) != (tcb_wrc_man.PHY = %p)", tcb_cmn_sub.PHY, tcb_wrc_man.PHY);
    if (tcb_cmn_sub.PHY != tcb_rdc_man.PHY)  $error("ERROR: %m parameter (tcb_cmn_sub.PHY = %p) != (tcb_rdc_man.PHY = %p)", tcb_cmn_sub.PHY, tcb_rdc_man.PHY);
  endgenerate
`endif

////////////////////////////////////////////////////////////////////////////////
// passthrough
////////////////////////////////////////////////////////////////////////////////

  // handshake valid
  assign tcb_rdc_man.vld = ~tcb_cmn_sub.req.wen & tcb_cmn_sub.vld;
  assign tcb_wrc_man.vld =  tcb_cmn_sub.req.wen & tcb_cmn_sub.vld;
  // handshake ready
  assign tcb_cmn_sub.rdy = ~tcb_cmn_sub.req.wen ? tcb_rdc_man.rdy
                                                : tcb_wrc_man.rdy;

  // request
  // TODO: avoid passing write data to read channel
  assign tcb_rdc_man.req =  tcb_cmn_sub.req;
  assign tcb_wrc_man.req =  tcb_cmn_sub.req;
  // response
  // TODO: avoid passing read data from write channel
  assign tcb_cmn_sub.rsp =  tcb_cmn_sub.dly[tcb_cmn_sub.PHY.DLY].ren ? tcb_rdc_man.rsp
                                                                     : tcb_wrc_man.rsp;

endmodule: tcb_lib_common2independent
