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
    TCB_PROCESSOR = 1'b0,  // always LSB aligned
    TCB_MEMORY    = 1'b1   // position depends on address
  } tcb_mode_t;

  // alignment
  typedef enum bit {
    TCB_UNALIGNED = 1'b0,  // unaligned
    TCB_ALIGNED   = 1'b1   // aligned
  } tcb_align_t;

  // bit vector order
  typedef enum bit {
    TCB_DESCENDING = 1'b0,  // descending order ([7:0])
    TCB_ASCENDING  = 1'b1   //  ascending order ([0:7])
  } tcb_order_t;

////////////////////////////////////////////////////////////////////////////////
// endianness
////////////////////////////////////////////////////////////////////////////////

  // endianness
  typedef enum bit {
    TCB_LITTLE = 1'b0,  // little-endian
    TCB_BIG    = 1'b1   // big-endian
  } tcb_endian_t;

endpackage: tcb_pkg