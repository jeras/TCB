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
    function automatic logic endianness (
        input logic ndn,  // requested endianness
        tcb_cfg_t   CFG   // configuration parameters
    );
        if ($isunknown(ndn)) begin
            // if desired endianness is undefined,
            // apply default endianness
            endianness = CFG.PCK.NDN;
        end else begin
            // apply desired endianness
            endianness = ndn;
            // check if endianness is supported
            if (!CFG.BUS.NDN) begin
                assert (ndn ==? CFG.PCK.NDN) else $error("Transaction endianness does not match CFG.BUS.NDN");
            end
        end
    endfunction: endianness

endpackage: tcb_vip_pkg