# System bus comparison

This document compares TCB against other common (standard) system busses,
and so some extent other system busses among themselves.

## Introduction

The following system busses are compared:

- AMBA APB
- AMBA AHB
- AMBA AXI4-Lite
- AMBA AXI5-Lite
- QMEM ([specification](https://somuch.guru/2016/06/28/qsoc-the-qmem-bus/) and [IP](https://github.com/rkrajnc/or1200-qmem)),
- Wishbone ([specification](https://opencores.org/howto/wishbone) version [B4](https://cdn.opencores.org/downloads/wbspec_b4.pdf))
- OBI ([OpenBus Interface specification](https://github.com/openhwgroup/obi) versions ..., [1.6](https://github.com/openhwgroup/obi/blob/main/OBI-v1.6.0.pdf))
- TileLink ([specification](https://www.sifive.com/documentation) version [1.9.3](https://www.sifive.com/document-file/tilelink-spec-1.9.3)).

Other system busses are mentioned but not used in the comparison.

- Open Core Protocol ([specification 3.0](https://accellera.org/downloads/standards/ocp)),
- CoreConnect from [IBM](https://web.archive.org/web/20090129183058/http://www-01.ibm.com/chips/techlib/techlib.nsf/products/CoreConnect_Bus_Architecture)
- Altera Avalon ()



### OBI (OpenBus Interface)

OBI originates from the [PULP Platform](https://pulp-platform.org/) project.
PULP Platform has a few [repositories](https://github.com/orgs/pulp-platform/repositories?q=obi)
implementing OBI interconnect and peripherals.

#### OpenHW Foundation

The [OpenHW Foundation](https://openhwfoundation.org/) adopted many PULP Platform cores
for the [CORE-V family of RISC-V cores](https://github.com/openhwgroup/core-v-cores).

The following CORE-V-CORES use OBI:
- Ibex (Zero-riscy) derivatives (2-stage pipeline):
  - [CVE2/CV32E20](https://github.com/openhwgroup/cve2) (Ibex fork)
  uses OBI for [instruction/data memory interfaces](https://github.com/openhwgroup/cve2/blob/main/rtl/cve2_top.sv#L34-L51):
  - no support for atomic instructions,
  - no PMP.
- RI5CY derivatives (4-stage pipeline):
  - [CV32E40P](https://github.com/openhwgroup/cv32e40p/tree/master)
    uses OBI for [instruction/data memory interfaces](https://github.com/openhwgroup/cv32e40p/blob/master/rtl/cv32e40p_core.sv):
    - no support for atomic instructions,
    - no PMP.
  - [CV32E40S](https://github.com/openhwgroup/cv32e40s)
    uses OBI for [instruction/data memory interfaces](https://github.com/openhwgroup/cv32e40s/blob/master/rtl/cv32e40s_core.sv#L69-L104):
    - no support for atomic instructions,
    - does have a PMP unit (additional `memtype` and `prot` interface signals),
    - parity/integrity interface signals.
  - [CV32E40X](https://github.com/openhwgroup/cv32e40x)
    uses OBI for [instruction/data memory interfaces](https://github.com/openhwgroup/cv32e40x/blob/master/rtl/cv32e40x_core.sv#L71-L96):
    - does support atomic instructions (additional `atop` load/store interface signal),
    - does have a PMP unit (additional `memtype` and `prot` interface signals).

Ibex based cores use an OBI compatible interface, but there are no explicit references to the name OBI.
The RI5CY derived cores internally use explicitly named OBI SystemVerilog interfaces.
All processors use OBI without backpressure (READY signal) on the response channel.

#### lowRISC

The [lowRISC® C.I.C. (Community Interest Company)] adopted
the [Ibex](https://github.com/lowRISC/ibex) core.
The core is primarily used within [OpenTitan®](https://opentitan.org/).

The OpenTitan SoC uses TileLink for the interconnect and peripherals.

The Ibex core itself uses an [unnamed custom bus](https://ibex-core.readthedocs.io/en/latest/02_user/integration.html#interfaces)
which is a compatible predecessor to OBI.
Both the [instruction fetch](https://ibex-core.readthedocs.io/en/latest/03_reference/instruction_fetch.html)
and [load/store](https://ibex-core.readthedocs.io/en/latest/03_reference/load_store_unit.html#load-store-unit) units
use a similar interface compatible with OBI, in both cases the response channel READY signal is hardwired to `1`.
Misaligned access is not supported (compressed instruction fetch is handled within the core).

The [Ibex Demo System](https://github.com/lowRISC/ibex-demo-system) uses a simplified version of the protocol
within the [interconnect](https://github.com/lowRISC/ibex/blob/master/shared/rtl/bus.sv),
which behaves like [TCB-Lite with `DLY=1`](https://github.com/lowRISC/ibex/blob/master/shared/rtl/bus.sv#L95).



# References

1. [Ibex RISC-V core load/store bus interface](https://ibex-core.readthedocs.io/en/latest/02_user/integration.html)
1. [NeoRV32 RISC-V core bus interface](https://stnolting.github.io/neorv32/#_bus_interface)
1. [AMBA on Wikipedia](https://en.wikipedia.org/wiki/Advanced_Microcontroller_Bus_Architecture)
1. [AMBA on ARM](https://developer.arm.com/Architectures/AMBA)
1. [Wishbone B4](https://cdn.opencores.org/downloads/wbspec_b4.pdf)
1. Pulp Platform Snitch [Reqrsp Interface](https://pulp-platform.github.io/snitch/rm/reqrsp_interface/)
1. OpenTitan [TileLink IP](https://docs.opentitan.org/hw/ip/tlul/doc/)
1. https://github.com/pulp-platform/obi?tab=readme-ov-file
