////////////////////////////////////////////////////////////////////////////////
// TCB (Tightly Coupled Bus) VIP (Verifivation IP) PacKaGe
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

  typedef logic         [8-1:0] dat_t [];

  typedef logic  [1-1:0][8-1:0] data8_t;
  typedef logic  [2-1:0][8-1:0] data16_t;
  typedef logic  [4-1:0][8-1:0] data32_t;
  typedef logic  [8-1:0][8-1:0] data64_t;
  typedef logic [16-1:0][8-1:0] data128_t;

  function automatic dat_t dat_f (
    input int unsigned    len,
    input logic [8/2-1:0] val = 'x
  );
    dat_f = new[len];
    for (int unsigned i=0; i<len; i++) begin
      dat_f[i] = {val, i[8/2-1:0]};
    end
  endfunction: dat_f;

  function automatic data8_t data8_f (
    input logic [8/2-1:0] val = 'x
  );
    for (int unsigned i=0; i<$clog2(8); i++) begin
      data8_f[i] = {val, i[8/2-1:0]};
    end
  endfunction: data8_f;

  function automatic data16_t data16_f (
    input logic [8/2-1:0] val = 'x
  );
    for (int unsigned i=0; i<$clog2(16); i++) begin
      data16_f[i] = {val, i[8/2-1:0]};
    end
  endfunction: data16_f;

  function automatic data32_t data32_f (
    input logic [8/2-1:0] val = 'x
  );
    for (int unsigned i=0; i<$clog2(32); i++) begin
      data32_f[i] = {val, i[8/2-1:0]};
    end
  endfunction: data32_f;

  function automatic data64_t data64_f (
    input logic [8/2-1:0] val = 'x
  );
    for (int unsigned i=0; i<$clog2(64); i++) begin
      data64_f[i] = {val, i[8/2-1:0]};
    end
  endfunction: data64_f;

  function automatic data128_t data128_f (
    input logic [8/2-1:0] val = 'x
  );
    for (int unsigned i=0; i<$clog2(128); i++) begin
      data128_f[i] = {val, i[8/2-1:0]};
    end
  endfunction: data128_f;

endpackage: tcb_vip_pkg