////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) SystemVerilog package
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

package tcb_pkg;

////////////////////////////////////////////////////////////////////////////////
// miscellaneous
////////////////////////////////////////////////////////////////////////////////

  // transaction sizes
  typedef enum {
    TCB_BYTE = 0,  //   8-bit byte
    TCB_HALF = 1,  //  16-bit half-word
    TCB_WORD = 2,  //  32-bit word
    TCB_DBLE = 3,  //  64-bit double-word
    TCB_QUAD = 4   // 128-bit quad-word
  } tcb_size_t;

////////////////////////////////////////////////////////////////////////////////
// size/mode/order/channel (used for compile time parameters)
////////////////////////////////////////////////////////////////////////////////

  // transfer size encoding
  typedef enum bit {
    TCB_LOGARITHMIC = 1'b0,  // logarithmic (2^n)
    TCB_LINEAR      = 1'b1   // linear (n)
  } tcb_par_size_t;

  // data position mode
  typedef enum bit {
    TCB_REFERENCE = 1'b0,  // always LSB aligned
    TCB_MEMORY    = 1'b1   // position depends on address
  } tcb_par_mode_t;

  // byte order
  typedef enum bit {
    TCB_DESCENDING = 1'b0,  // descending order
    TCB_ASCENDING  = 1'b1   //  ascending order
  } tcb_par_order_t;

  // channel configuration
  typedef enum bit [1:0] {
    // 2 bit value {rd,wr}
    TCB_COMMON_HALF_DUPLEX  = 2'b00,  // common channel with half duplex read/write
    TCB_COMMON_FULL_DUPLEX  = 2'b11,  // common channel with full duplex read/write
    TCB_INDEPENDENT_WRITE   = 2'b01,  // independent write channel
    TCB_INDEPENDENT_READ    = 2'b10   // independent read channel
  } tcb_par_channel_t;

////////////////////////////////////////////////////////////////////////////////
// parameter structure
////////////////////////////////////////////////////////////////////////////////

  // physical interface parameter structure
  // TODO: the structure is packed to workaround a Verilator bug
  typedef struct packed {
    // protocol
    int unsigned      DLY;  // response delay
    // signal widths
    int unsigned      SLW;  // selection   width (byte width is 8 by default)
    int unsigned      ABW;  // address bus width
    int unsigned      DBW;  // data    bus width
    int unsigned      ALW;  // alignment width
    // data packing parameters
    tcb_par_size_t    SIZ;  // transfer size encoding
    tcb_par_mode_t    MOD;  // data position mode
    tcb_par_order_t   ORD;  // byte order
    // channel configuration
    tcb_par_channel_t CHN;  // channel configuration
  } tcb_par_phy_t;

  // physical interface parameter default
  localparam tcb_par_phy_t TCB_PAR_PHY_DEF = '{
    // protocol
    DLY: 0,
    // signal widths
    SLW: 8,
    ABW: 32,
    DBW: 32,
    ALW: 2,   // $clog2(DBW/SLW)
    // data packing parameters
    SIZ: TCB_LOGARITHMIC,
    MOD: TCB_MEMORY,
    ORD: TCB_DESCENDING,
    // channel configuration
    CHN: TCB_COMMON_HALF_DUPLEX
  };

////////////////////////////////////////////////////////////////////////////////
// parameter structure validation function
////////////////////////////////////////////////////////////////////////////////

  // check for equivalence
  function automatic int tcb_par_phy_match(
    tcb_par_phy_t phy_val,
    tcb_par_phy_t phy_ref   // reference can contain wildcard values
  );
    // status structure
    struct packed {
      bit DLY;
      bit SLW;
      bit ABW;
      bit DBW;
      bit ALW;
      bit SIZ;
      bit MOD;
      bit ORD;
      bit CHN;
    } status;

    // comparison
    status.DLY = phy_val.DLY ==? phy_ref.DLY;
    status.SLW = phy_val.SLW ==? phy_ref.SLW;
    status.ABW = phy_val.ABW ==? phy_ref.ABW;
    status.DBW = phy_val.DBW ==? phy_ref.DBW;
    status.ALW = phy_val.ALW ==? phy_ref.ALW;
    status.SIZ = phy_val.SIZ ==? phy_ref.SIZ;
    status.MOD = phy_val.MOD ==? phy_ref.MOD;
    status.ORD = phy_val.ORD ==? phy_ref.ORD;
    status.CHN = phy_val.CHN ==? phy_ref.CHN;

    // reporting validation status
    if (status.DLY)  $error("parameter mismatch PHY.DLY=%d != PHY.DLY=%d", phy_val.DLY, phy_ref.DLY);
    if (status.SLW)  $error("parameter mismatch PHY.SLW=%d != PHY.SLW=%d", phy_val.SLW, phy_ref.SLW);
    if (status.ABW)  $error("parameter mismatch PHY.ABW=%d != PHY.ABW=%d", phy_val.ABW, phy_ref.ABW);
    if (status.DBW)  $error("parameter mismatch PHY.DBW=%d != PHY.DBW=%d", phy_val.DBW, phy_ref.DBW);
    if (status.ALW)  $error("parameter mismatch PHY.ALW=%d != PHY.ALW=%d", phy_val.ALW, phy_ref.ALW);
    if (status.SIZ)  $error("parameter mismatch PHY.SIZ=%d != PHY.SIZ=%d", phy_val.SIZ, phy_ref.SIZ);
    if (status.MOD)  $error("parameter mismatch PHY.MOD=%d != PHY.MOD=%d", phy_val.MOD, phy_ref.MOD);
    if (status.ORD)  $error("parameter mismatch PHY.ORD=%d != PHY.ORD=%d", phy_val.ORD, phy_ref.ORD);
    if (status.CHN)  $error("parameter mismatch PHY.CHN=%d != PHY.CHN=%d", phy_val.CHN, phy_ref.CHN);

    // return simple status
    return(|status);
  endfunction: tcb_par_phy_match

////////////////////////////////////////////////////////////////////////////////
// parameter structure debug function
////////////////////////////////////////////////////////////////////////////////

  // print out parameter structure
  function automatic void tcb_par_phy_print(
    tcb_par_phy_t phy_val
  );
    // reporting validation status
    $info("parameter PHY.DLY=%d", phy_val.DLY);
    $info("parameter PHY.SLW=%d", phy_val.SLW);
    $info("parameter PHY.ABW=%d", phy_val.ABW);
    $info("parameter PHY.DBW=%d", phy_val.DBW);
    $info("parameter PHY.ALW=%d", phy_val.ALW);
    $info("parameter PHY.SIZ=%s", phy_val.SIZ.name());
    $info("parameter PHY.MOD=%s", phy_val.MOD.name());
    $info("parameter PHY.ORD=%s", phy_val.ORD.name());
    $info("parameter PHY.CHN=%s", phy_val.CHN.name());
  endfunction: tcb_par_phy_print

////////////////////////////////////////////////////////////////////////////////
// endianness (used for runtime signal values)
////////////////////////////////////////////////////////////////////////////////

  // endianness
  typedef enum logic {
    TCB_LITTLE = 1'b0,  // little-endian
    TCB_BIG    = 1'b1   // big-endian
  } tcb_cfg_endian_t;

////////////////////////////////////////////////////////////////////////////////
// default structures containing optional signals
////////////////////////////////////////////////////////////////////////////////

  // command
  typedef struct packed {
    logic inc;  // incremented address
    logic rpt;  // repeated address
    logic lck;  // arbitration lock
  } tcb_req_cmd_def_t;

  // status
  typedef struct packed {
    logic err;  // error response
  } tcb_rsp_sts_def_t;

endpackage: tcb_pkg
