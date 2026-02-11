////////////////////////////////////////////////////////////////////////////////
// SPI master model
////////////////////////////////////////////////////////////////////////////////
// Copyright 2025 Iztok Jeras
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

package spi_pkg;

    typedef struct packed {
        logic cpol;  // Clock POLarity
        logic cpha;  // Clock PHAse
    } spi_mode_t;

    typedef enum logic [1:0] {
        SPI_MODE0 = 2'b00,  // {cpol: 1'b0, cpha: 1'b0}
        SPI_MODE1 = 2'b01,  // {cpol: 1'b0, cpha: 1'b1}
        SPI_MODE2 = 2'b10,  // {cpol: 1'b1, cpha: 1'b0}
        SPI_MODE3 = 2'b11   // {cpol: 1'b1, cpha: 1'b1}
    } spi_mode_e;

    typedef enum logic {
        SPI_HALF = 1'b0,
        SPI_FULL = 1'b1
    } spi_duplex_e;

    typedef enum logic [1:0] {
        SPI_SINGLE = 2'b00,
        SPI_DUAL   = 2'b01,
        SPI_QUAD   = 2'b10,
        SPI_OCTA   = 2'b11
    } spi_width_e;

endpackage: spi_pkg
