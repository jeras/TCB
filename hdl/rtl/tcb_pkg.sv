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

  // channel configuration
  typedef enum bit [2-1:0] {
    // 2 bit value {rd,wr}
    TCB_CHN_HALF_DUPLEX = 2'b00,  // half duplex read/write (wen is used to distinguish between write and read)
    TCB_CHN_FULL_DUPLEX = 2'b11,  // full duplex read/write (wen/ren are both used)
    TCB_CHN_WRITE_ONLY  = 2'b01,  // write only channel (wen/ren are both ignored)
    TCB_CHN_READ_ONLY   = 2'b10   // read  only channel (wen/ren are both ignored)
  } tcb_bus_channel_t;

  // prefetch configuration
  typedef enum bit {
    TCB_PRF_DISABLED = 1'b0,  //
    TCB_PRF_ENABLED  = 1'b1   // enable prefetch signals
  } tcb_bus_prefetch_t;

  // next address configuration (for misaligned accesses)
  typedef enum bit {
    TCB_NXT_DISABLED = 1'b0,  //
    TCB_NXT_ENABLED  = 1'b1   // enable prefetch signals
  } tcb_bus_next_t;

  // data sizing mode
  typedef enum bit {
    TCB_MOD_LOG_SIZE = 1'b0,  // logarithmic size
    TCB_MOD_BYTE_ENA = 1'b1   // byte enable
  } tcb_bus_mode_t;

  // byte order
  typedef enum bit {
    TCB_ORD_DESCENDING = 1'b0,  // descending order
    TCB_ORD_ASCENDING  = 1'b1   //  ascending order
  } tcb_bus_order_t;

  // endianness configuration
  typedef enum bit [2-1:0] {
    BCB_NDN_DEFAULT = 2'b00,  // default derived from byte order
    TCB_NDN_LITTLE  = 2'b01,  // little endian only (default for TCB_ORD_DESCENDING order)
    TCB_NDN_BIG     = 2'b10,  // big    endian only (default for TCB_ORD_ASCENDING  order)
    TCB_NDN_BI_NDN  = 2'b11   // bi-    endian support
  } tcb_bus_endian_t;

  // bus layer parameter structure
  // TODO: the structure is packed to workaround a Verilator bug
  `ifdef VERILATOR
  typedef struct packed {
  `else
  typedef struct {
  `endif
    int unsigned       ADR;  // address width
    int unsigned       DAT;  // data width
    int unsigned       FRM;  // framing maximum length (if 0 framing is disabled)
    tcb_bus_channel_t  CHN;  // channel configuration
    tcb_bus_prefetch_t PRF;  // prefetch configuration
    tcb_bus_next_t     NXT;  // next address configuration
    tcb_bus_mode_t     MOD;  // data sizing mode
    tcb_bus_order_t    ORD;  // byte order
    tcb_bus_endian_t   NDN;  // endianness configuration
  } tcb_bus_t;

  // physical interface parameter default
  localparam tcb_bus_t TCB_BUS_DEF = '{
    ADR: 32,
    DAT: 32,
    FRM: 15, // frame size of up to FRM+1=16 transfers
    CHN: TCB_CHN_HALF_DUPLEX,
    PRF: TCB_PRF_ENABLED,
    NXT: TCB_NXT_ENABLED,
    MOD: TCB_MOD_BYTE_ENA,
    ORD: TCB_ORD_DESCENDING,
    NDN: TCB_NDN_BI_NDN
  };

////////////////////////////////////////////////////////////////////////////////
// packing layer (defines the relations between bus signals)
////////////////////////////////////////////////////////////////////////////////

  // bus parameter structure
  `ifdef VERILATOR
  typedef struct packed {
  `else
  typedef struct {
  `endif
    int unsigned      MIN;  // minimum transfer logarithmic size
    int unsigned      OFF;  // number of zeroed offset bits
    int unsigned      ALN;  // alignment (number of aligned address bits)
  } tcb_pck_t;

  // physical interface parameter default
  localparam tcb_pck_t TCB_PCK_DEF = '{
    MIN: 0,   // maximum $clog2(BUS_DAT/8)
    OFF: 0,   // maximum $clog2(BUS_DAT/8)
    ALN: 0    // maximum $clog2(BUS_DAT/8)
  };

  // endianness packing (used for runtime signal values)
  typedef enum logic {
    TCB_LITTLE = 1'b0,  // little-endian
    TCB_BIG    = 1'b1   // big-endian
  } tcb_endian_t;

////////////////////////////////////////////////////////////////////////////////
// default structures containing all optional signals
////////////////////////////////////////////////////////////////////////////////

  // TODO: rethink the response status
  // status
  typedef struct packed {
    logic err;  // error response
  } tcb_rsp_sts_t;

////////////////////////////////////////////////////////////////////////////////
// perameterized types
////////////////////////////////////////////////////////////////////////////////

  virtual class tcb_c #(
    parameter  int unsigned DLY = TCB_HSK_DEF,
    parameter  tcb_bus_t    BUS = TCB_BUS_DEF,
    parameter  tcb_pck_t    PCK = TCB_PCK_DEF
  );
    // signal widths
    localparam BUS_LEN = $clog2(BUS.FRM+1);
    localparam BUS_BEN = BUS.DAT/8;
    localparam BUS_MAX = $clog2(BUS_BEN);
    localparam BUS_SIZ = $clog2(BUS_MAX+1);

    localparam int unsigned LEFT  = (BUS.ORD == TCB_ORD_DESCENDING) ? BUS_BEN-1 : 0;
    localparam int unsigned RIGHT = (BUS.ORD == TCB_ORD_DESCENDING) ? 0 : BUS_BEN-1;

    typedef logic [LEFT:RIGHT]        ben_t;
    typedef logic [LEFT:RIGHT][8-1:0] dat_t;

    // request
    typedef struct packed {
      // framing
      logic               frm;  // frame
      logic [BUS_LEN-1:0] len;  // frame length
      // channel
      logic               wen;  // write enable
      logic               ren;  // read enable
      // prefetch
      logic               rpt;  // repeated address
      logic               inc;  // incremented address
      // address and next address
      logic [BUS.ADR-1:0] adr;  // current address
      logic [BUS.ADR-1:0] nxt;  // next address
      // data sizing
      logic [BUS_SIZ-1:0] siz;  // logarithmic transfer size
      ben_t               ben;  // byte enable
      // endianness
      logic               ndn;  // endianness
      // data
      dat_t               wdt;  // write data
    } req_t;

    // response
    typedef struct packed {
      dat_t               rdt;  // read data
      tcb_rsp_sts_t       sts;  // status
    } rsp_t;
  endclass: tcb_c

////////////////////////////////////////////////////////////////////////////////
// predefined types
////////////////////////////////////////////////////////////////////////////////

//  typedef tcb_c #(.ADR (32), .DAT (32))::req_t tcb_req_t;  // request
//  typedef tcb_c #(.ADR (32), .DAT (32))::req_t tcb_rsp_t;  // response

////////////////////////////////////////////////////////////////////////////////
// predefined types
////////////////////////////////////////////////////////////////////////////////

  // default signal widths
  localparam DEF_LEN = $clog2(TCB_BUS_DEF.FRM+1);
  localparam DEF_ADR = 32;
  localparam DEF_DAT = 32;
  localparam DEF_BEN = DEF_DAT/8;
  localparam DEF_MAX = $clog2(DEF_BEN);
  localparam DEF_SIZ = $clog2(DEF_MAX+1);

  // request
  typedef struct packed {
    // framing
    logic                      frm;  // frame
    logic [DEF_LEN-1:0]        len;  // frame length
    // channel
    logic                      wen;  // write enable
    logic                      ren;  // read enable
    // prefetch
    logic                      rpt;  // repeated address
    logic                      inc;  // incremented address
    // address and next address
    logic [DEF_ADR-1:0]        adr;  // current address
    logic [DEF_ADR-1:0]        nxt;  // next address
    // data sizing
    logic [DEF_SIZ-1:0]        siz;  // logarithmic transfer size
    logic [DEF_BEN-1:0]        ben;  // byte enable
    // endianness
    logic                      ndn;  // endianness
    // data
    logic [DEF_BEN-1:0][8-1:0] wdt;  // write data
  } tcb_req_t;

  // response
  typedef struct packed {
    logic [DEF_BEN-1:0][8-1:0] rdt;  // read data
    tcb_rsp_sts_t              sts;  // status
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
