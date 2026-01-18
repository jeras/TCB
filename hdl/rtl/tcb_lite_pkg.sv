////////////////////////////////////////////////////////////////////////////////
// TCB-Lite (Tightly Coupled Bus) SystemVerilog package
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

package tcb_lite_pkg;

////////////////////////////////////////////////////////////////////////////////
// handshake layer (defines the response delay and stability)
////////////////////////////////////////////////////////////////////////////////

    // parameter structure
    typedef struct {
        int unsigned DLY;  // response delay
        bit          HLD;  // response hold (till the next access, response data even further till the next read access)
    } tcb_lite_hsk_t;

    // parameter defaults
    localparam tcb_lite_hsk_t TCB_LITE_HSK_DEF = '{
        DLY:    1,
        HLD: 1'b0
    };

////////////////////////////////////////////////////////////////////////////////
// bus layer (defines which signal subset is used)
////////////////////////////////////////////////////////////////////////////////

    // parameter structure
    typedef struct {
        bit          MOD;  // mode (0-logarithmic size, 1-byte enable)
        int unsigned CTL;  // control width (user defined request signals)
        int unsigned ADR;  // address width
        int unsigned DAT;  // data    width
        int unsigned STS;  // status  width (user defined response signals)
    } tcb_lite_bus_t;

    // physical interface parameter default
    localparam tcb_lite_bus_t TCB_LITE_BUS_DEF = '{
        MOD: 1'b0,
        CTL:    0,
        ADR:   32,
        DAT:   32,
        STS:    0
    };

////////////////////////////////////////////////////////////////////////////////
// TCB configuration structure
////////////////////////////////////////////////////////////////////////////////

    // PMA parameter structure
    typedef struct {
        tcb_lite_hsk_t HSK;  // handshake
        tcb_lite_bus_t BUS;  // bus
    } tcb_lite_cfg_t;

    // configuration parameter default
    localparam tcb_lite_cfg_t TCB_LITE_CFG_DEF = '{
        HSK: TCB_LITE_HSK_DEF,
        BUS: TCB_LITE_BUS_DEF
    };

////////////////////////////////////////////////////////////////////////////////
// predefined types
////////////////////////////////////////////////////////////////////////////////

//  typedef tcb_c #(.ADR (32), .DAT (32))::req_t tcb_req_t;  // request
//  typedef tcb_c #(.ADR (32), .DAT (32))::req_t tcb_rsp_t;  // response

////////////////////////////////////////////////////////////////////////////////
// miscellaneous
////////////////////////////////////////////////////////////////////////////////

    // TODO: this is actually a RISC-V definition
    // atomic encoding
    typedef enum logic [5-1:0] {
        LR      = 5'b00010,
        SC      = 5'b00011,
        AMOSWAP = 5'b00001,
        AMOADD  = 5'b00000,
        AMOXOR  = 5'b00100,
        AMOAND  = 5'b01100,
        AMOOR   = 5'b01000,
        AMOMIN  = 5'b10000,
        AMOMAX  = 5'b10100,
        AMOMINU = 5'b11000,
        AMOMAXU = 5'b11100
    } tcb_lite_amo_t;

endpackage: tcb_lite_pkg
