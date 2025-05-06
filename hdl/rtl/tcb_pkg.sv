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
// handshake layer (defines the response delay)
////////////////////////////////////////////////////////////////////////////////

  // handshake delay (HSK_DLY) default value
  localparam int unsigned TCB_HSK_DEF = 1;

////////////////////////////////////////////////////////////////////////////////
// bus layer (defines which signal subset is used)
////////////////////////////////////////////////////////////////////////////////

  // data position/sizing mode
  typedef enum bit {
    TCB_LOG_SIZE = 1'b0,  // logarithmic size
    TCB_BYTE_ENA = 1'b1   // byte enable
  } tcb_bus_mode_t;

  // channel configuration
  typedef enum bit [2-1:0] {
    // 2 bit value {rd,wr}
    TCB_HALF_DUPLEX = 2'b00,  // half duplex read/write (wen is used to distinguish between write and read)
    TCB_FULL_DUPLEX = 2'b11,  // full duplex read/write (wen/ren are both used)
    TCB_WRITE_ONLY  = 2'b01,  // write only channel (wen/ren are both ignored)
    TCB_READ_ONLY   = 2'b10   // read  only channel (wen/ren are both ignored)
  } tcb_bus_channel_t;

//  // prefetch configuration
//  typedef enum bit {
//    TCB_PREFETCH = 1'b0,  // logarithmic size
//    TCB_PREFETCH = 1'b1   // byte enable
//  } tcb_bus_prefetch_t;

////////////////////////////////////////////////////////////////////////////////
// protocol layer (defines the relations between bus signals)
////////////////////////////////////////////////////////////////////////////////

  // byte order
  typedef enum bit {
    TCB_DESCENDING = 1'b0,  // descending order
    TCB_ASCENDING  = 1'b1   //  ascending order
  } tcb_bus_order_t;

////////////////////////////////////////////////////////////////////////////////
// bus protocol parameter structure
////////////////////////////////////////////////////////////////////////////////

  // TODO: the structure is packed to workaround a Verilator bug
  typedef struct packed {
    // bus layer
    tcb_bus_channel_t CHN;  // channel configuration
    tcb_bus_mode_t    MOD;  // data position mode
    // data packing parameters
    int unsigned      ALN;  // alignment (number of aligned address bits)
    int unsigned      MIN;  // minimum transfer logarithmic size
    int unsigned      OFF;  // number of zeroed offset bits
    tcb_bus_order_t   ORD;  // byte order
  } tcb_bus_t;

////////////////////////////////////////////////////////////////////////////////
// BUS parameter structure
////////////////////////////////////////////////////////////////////////////////

  // physical interface parameter default
  localparam tcb_bus_t TCB_BUS_DEF = '{
    // bus layer
    CHN: TCB_HALF_DUPLEX,
    MOD: TCB_BYTE_ENA,
    // data packing parameters
    ALN: 0,   // maximum $clog2(DAT/UNT)
    MIN: 0,   // maximum $clog2(DAT/UNT)
    OFF: 0,   // maximum $clog2(DAT/UNT)
    ORD: TCB_DESCENDING
  };

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
    logic lck;  // arbitration lock (TODO: rename into frame)
  } tcb_req_cmd_t;

  // status
  typedef struct packed {
    logic err;  // error response
  } tcb_rsp_sts_t;

  // request
  typedef struct packed {
    tcb_req_cmd_t        cmd;  // command (optional)
    logic                wen;  // write enable
    logic                ren;  // read enable
    logic                ndn;  // endianness
    logic       [32-1:0] adr;  // address
    logic        [2-1:0] siz;  // logarithmic transfer size
    logic        [4-1:0] ben;  // byte enable
    logic [4-1:0][8-1:0] wdt;  // write data
  } tcb_req_t;

  // request
  typedef struct packed {
    logic [4-1:0][8-1:0] rdt;  // read data
    tcb_rsp_sts_t        sts;  // status
  } tcb_rsp_t;

////////////////////////////////////////////////////////////////////////////////
// miscellaneous
////////////////////////////////////////////////////////////////////////////////

  // transaction sizes
  typedef enum {
    TCB_BYTE = 0,  //   8-bit byte
    TCB_HALF = 1,  //  16-bit half-word
    TCB_WORD = 2,  //  32-bit word
    TCB_DBLE = 3,  //  64-bit double-word
    TCB_QUAD = 4,  // 128-bit quad-word
    TCB_OCTA = 8   // 256-bit octa-word
  } tcb_size_t;

endpackage: tcb_pkg
