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
// mode/alignment/order are compile time parameters
////////////////////////////////////////////////////////////////////////////////

  // byte/half/word/double/quad position inside data bus vector
  typedef enum bit {
    TCB_REFERENCE = 1'b0,  // always LSB aligned
    TCB_MEMORY    = 1'b1   // position depends on address
  } tcb_par_mode_t;

  // transfer size encoding
  typedef enum bit {
    TCB_LOGARITHMIC = 1'b0,  // logarithmic (2^n)
    TCB_LINEAR      = 1'b1   // linear (n)
  } tcb_par_size_t;

  // alignment
  typedef enum bit {
    TCB_UNALIGNED = 1'b0,  // unaligned
    TCB_ALIGNED   = 1'b1   // aligned
  } tcb_par_align_t;

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
  // TODO: tre structure is packed to workaround Verilator bug
  typedef struct packed {
    // signal bus widths
    int unsigned    SLW;  // selection   width (byte width is 8 by default)
    int unsigned    ABW;  // address bus width
    int unsigned    DBW;  // data    bus width
    // TCB parameters
    int unsigned    DLY;  // response delay
    // mode/alignment/order parameters
    tcb_par_mode_t  MOD;  // byte/half/word/double/quad position inside data bus vector
    tcb_par_size_t  SIZ;  // transfer size encoding
    tcb_par_align_t LGN;  // alignment
    tcb_par_order_t ORD;  // byte order
  } tcb_par_phy_t;

  // physical interface parameter default
  localparam tcb_par_phy_t TCB_PAR_PHY_DEF = '{
    // signal bus widths
    SLW: 8,
    ABW: 32,
    DBW: 32,
    // TCB parameters
    DLY: 1,
    // mode/alignment/order parameters
    MOD: TCB_REFERENCE,
    SIZ: TCB_LOGARITHMIC,
    LGN: TCB_ALIGNED,
    ORD: TCB_DESCENDING
  };

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
