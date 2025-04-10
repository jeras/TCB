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

  // data position mode
  typedef enum bit {
    TCB_RISC_V = 1'b0,  // RISC-V
    TCB_MEMORY = 1'b1   // memory
  } tcb_par_mode_t;

  // byte order
  typedef enum bit {
    TCB_DESCENDING = 1'b0,  // descending order
    TCB_ASCENDING  = 1'b1   //  ascending order
  } tcb_par_order_t;

  // channel configuration
  typedef enum bit [2-1:0] {
    // 2 bit value {rd,wr}
    TCB_COMMON_HALF_DUPLEX = 2'b00,  // common channel with half duplex read/write
    TCB_COMMON_FULL_DUPLEX = 2'b11,  // common channel with full duplex read/write
    TCB_INDEPENDENT_WRITE  = 2'b01,  // independent write channel
    TCB_INDEPENDENT_READ   = 2'b10   // independent read channel
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
    int unsigned      UNT;  // data unit width (byte width is 8 by default)
    int unsigned      ADR;  // address   width
    int unsigned      DAT;  // data      width
    int unsigned      ALN;  // alignment width
    // data packing parameters
    tcb_par_order_t   ORD;  // byte order
    tcb_par_mode_t    MOD;  // data position mode
    // channel configuration
    tcb_par_channel_t CHN;  // channel configuration
  } tcb_par_phy_t;

  // physical interface parameter default
  localparam tcb_par_phy_t TCB_PAR_PHY_DEF = '{
    // protocol
    DLY: 0,
    // signal widths
    UNT: 8,
    ADR: 32,
    DAT: 32,
    ALN: 2,   // $clog2(DAT/UNT)
    // data packing parameters
    ORD: TCB_DESCENDING,
    MOD: TCB_MEMORY,
    // channel configuration
    CHN: TCB_COMMON_HALF_DUPLEX
  };

////////////////////////////////////////////////////////////////////////////////
// parameter structure validation tasks functions
////////////////////////////////////////////////////////////////////////////////

  // check for equivalence
  function automatic tcb_par_phy_match(
    tcb_par_phy_t phy_val,
    tcb_par_phy_t phy_ref   // reference can contain wildcard values
  );
    // status structure
    struct packed {
      bit DLY;
      bit UNT;
      bit ADR;
      bit DAT;
      bit ALN;
      bit SIZ;
      bit ORD;
      bit MOD;
      bit CHN;
    } status;

    // comparison
    status.DLY = phy_val.DLY ==? phy_ref.DLY;
    status.UNT = phy_val.UNT ==? phy_ref.UNT;
    status.ADR = phy_val.ADR ==? phy_ref.ADR;
    status.DAT = phy_val.DAT ==? phy_ref.DAT;
    status.ALN = phy_val.ALN ==? phy_ref.ALN;
    status.ORD = phy_val.ORD ==? phy_ref.ORD;
    status.MOD = phy_val.MOD ==? phy_ref.MOD;
    status.CHN = phy_val.CHN ==? phy_ref.CHN;

    // reporting validation status
    if (status.DLY)  $error("parameter mismatch PHY.DLY=%d != PHY.DLY=%d", phy_val.DLY, phy_ref.DLY);
    if (status.UNT)  $error("parameter mismatch PHY.UNT=%d != PHY.UNT=%d", phy_val.UNT, phy_ref.UNT);
    if (status.ADR)  $error("parameter mismatch PHY.ADR=%d != PHY.ADR=%d", phy_val.ADR, phy_ref.ADR);
    if (status.DAT)  $error("parameter mismatch PHY.DAT=%d != PHY.DAT=%d", phy_val.DAT, phy_ref.DAT);
    if (status.ALN)  $error("parameter mismatch PHY.ALN=%d != PHY.ALN=%d", phy_val.ALN, phy_ref.ALN);
    if (status.ORD)  $error("parameter mismatch PHY.ORD=%d != PHY.ORD=%d", phy_val.ORD, phy_ref.ORD);
    if (status.MOD)  $error("parameter mismatch PHY.MOD=%d != PHY.MOD=%d", phy_val.MOD, phy_ref.MOD);
    if (status.CHN)  $error("parameter mismatch PHY.CHN=%d != PHY.CHN=%d", phy_val.CHN, phy_ref.CHN);

    // return simple status
    return(|status);
  endfunction: tcb_par_phy_match

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
