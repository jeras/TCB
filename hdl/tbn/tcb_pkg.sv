////////////////////////////////////////////////////////////////////////////////
// TCB: Tightly Coupled Bus package
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

  localparam int unsigned AW = 32;    // address width
  localparam int unsigned DW = 32;    // data    width
  localparam int unsigned BW = DW/8;  // byte e. width

  typedef struct packed {
    // TCB signals
    logic          wen;  // write enable
    logic [AW-1:0] adr;  // address
    logic [BW-1:0] ben;  // byte enable
    logic [DW-1:0] wdt;  // write data
    // timing
    int unsigned   len;  // wait length
  } tcb_req_t;

  typedef struct packed {
    // TCB signals
    logic [DW-1:0] rdt;  // read data
    logic          err;  // error
    // timing
    int unsigned   len;  // wait length
  } tcb_rsp_t;

endpackage: tcb_pkg