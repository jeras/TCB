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
// size/mode/order are compile time parameters
////////////////////////////////////////////////////////////////////////////////

  // transfer size encoding
  typedef enum bit {
    TCB_LOGARITHMIC = 1'b0,  // logarithmic (2^n)
    TCB_LINEAR      = 1'b1   // linear (n)
  } tcb_par_size_t;

  // byte/half/word/double/quad position inside data bus vector
  typedef enum bit {
    TCB_REFERENCE = 1'b0,  // always LSB aligned
    TCB_MEMORY    = 1'b1   // position depends on address
  } tcb_par_mode_t;

  // byte order
  typedef enum bit {
    TCB_DESCENDING = 1'b0,  // descending order
    TCB_ASCENDING  = 1'b1   //  ascending order
  } tcb_par_order_t;

////////////////////////////////////////////////////////////////////////////////
// endianness
////////////////////////////////////////////////////////////////////////////////

  // endianness
  typedef enum logic {
    TCB_LITTLE = 1'b0,  // little-endian
    TCB_BIG    = 1'b1   // big-endian
  } tcb_cfg_endian_t;

////////////////////////////////////////////////////////////////////////////////
// parameter structure
////////////////////////////////////////////////////////////////////////////////

  // physical interface parameter structure
  // TODO: the structure is packed to workaround a Verilator bug
  typedef struct packed {
    // protocol
    int unsigned    DLY;  // response delay
    // signal widths
    int unsigned    SLW;  // selection   width (byte width is 8 by default)
    int unsigned    ABW;  // address bus width
    int unsigned    DBW;  // data    bus width
    int unsigned    ALW;  // alignment width
    // data packing parameters
    tcb_par_size_t  SIZ;  // transfer size encoding
    tcb_par_mode_t  MOD;  // byte/half/word/double/quad position inside data bus vector
    tcb_par_order_t ORD;  // byte order
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
    MOD: TCB_REFERENCE,
    ORD: TCB_DESCENDING
  };

////////////////////////////////////////////////////////////////////////////////
// parameter structure validation tasks functions
////////////////////////////////////////////////////////////////////////////////

  function automatic int validation_error (string str);
    return($error("ERROR: %m: %s", str));
  endfunction: validation_error

  // check for equivalence
  function automatic tcb_par_phy_match(
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

    // reporting validation status
    if (status.DLY)  validation_error($sformatf("parameter mismatch PHY.DLY=%d != PHY.DLY=%d", phy_val.DLY, phy_ref.DLY));
    if (status.SLW)  validation_error($sformatf("parameter mismatch PHY.SLW=%d != PHY.SLW=%d", phy_val.SLW, phy_ref.SLW));
    if (status.ABW)  validation_error($sformatf("parameter mismatch PHY.ABW=%d != PHY.ABW=%d", phy_val.ABW, phy_ref.ABW));
    if (status.DBW)  validation_error($sformatf("parameter mismatch PHY.DBW=%d != PHY.DBW=%d", phy_val.DBW, phy_ref.DBW));
    if (status.ALW)  validation_error($sformatf("parameter mismatch PHY.ALW=%d != PHY.ALW=%d", phy_val.ALW, phy_ref.ALW));
    if (status.SIZ)  validation_error($sformatf("parameter mismatch PHY.SIZ=%d != PHY.SIZ=%d", phy_val.SIZ, phy_ref.SIZ));
    if (status.MOD)  validation_error($sformatf("parameter mismatch PHY.MOD=%d != PHY.MOD=%d", phy_val.MOD, phy_ref.MOD));
    if (status.ORD)  validation_error($sformatf("parameter mismatch PHY.ORD=%d != PHY.ORD=%d", phy_val.ORD, phy_ref.ORD));

    // return simple status
    return(|status);
  endfunction: tcb_par_phy_match

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
