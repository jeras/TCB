////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verification IP) miscelaneous package
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

package tcb_vip_pkg;

    import tcb_pkg::*;

    // endianness
    // NOTE: If the bus endianness is hardcoded, the transaction endianness must:
    //       - match the hardcoded bus endianness OR,
    //       - be undefined (x/z).
    // NOTE: If the requested endianness $isunknown, the transaction endianness
    //       will be set to the native bus endianness.
    function automatic logic endianness (
        input logic ndn,  // requested endianness
        tcb_cfg_t   CFG   // configuration parameters
    );
        case (CFG.BUS.NDN)
            TCB_NDN_DEFAULT: begin
                endianness = CFG.BUS.ORD;
                assert (endianness ==? ndn) else $error("Transaction endianness does not match CFG.BUS.NDN");
            end
            TCB_NDN_BI_NDN :  begin
                if ($isunknown(ndn)) begin
                    endianness = CFG.BUS.ORD;
                end else begin
                    endianness = ndn;
                end
            end
            TCB_NDN_LITTLE ,
            TCB_NDN_BIG    :  begin
                endianness = CFG.BUS.NDN[0];
                assert (endianness ==? ndn) else $error("Transaction endianness does not match CFG.BUS.NDN");
            end
        endcase
    endfunction: endianness

endpackage: tcb_vip_pkg