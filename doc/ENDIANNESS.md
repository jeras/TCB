# [Endianness](https://en.wikipedia.org/wiki/Endianness)

To better understand big-endian design requirements,
I collected information from some well known big-endian and bi-endian architectures,
with the focus on ones with an open source implementation,
so I could observe both specification and implementation.

## Ascending vs. descending bit order for vectors and register fields

The question is whether it is common for big-endian architectures
to have bit vectors defined in ascending bit order
as opposed to a more common descending bit order.
Both vector definitions have the MSB value on the left
and the LSB value on the right.

| oder       | range     | SystemVerilog     | VHDL                                |
|------------|-----------|-------------------|-------------------------------------|
| ascending  | MSB < LSB | `logic [MSB:LSB]` | `std_logic_vector (MSB     to LSB)` |
| descending | MSB > LSB | `logic [MSB:LSB]` | `std_logic_vector (MSB downto LSB)` |

Example for 32-bit vectors.

| oder       | SystemVerilog    | VHDL                                  |
|------------|------------------|---------------------------------------|
| ascending  | `logic [0:32-1]` | `std_logic_vector (0        to 32-1)` |
| descending | `logic [32-1:0]` | `std_logic_vector (32-1 downto 0   )` |

NOTE: The *ascending/descending bit range* terminology is used in the SystemVerilog standard.

Three big-endian architectures with open source RTL implementations were observed:
- OpenRISC,
- OpenSPARC,
- OpenPOWER.

Only OpenPOWER is using ascending order.
It is using it extensively in documentation for:
- general purpose register file,
- register field specifications in the documentation,
- ...
And in RTL for:
- all (there might be some exceptions) internal vectors,
- internal custom system bus address, data and byte enable,
- ...

At the edge of the core bridges convert
the internal ascending order into descending order for:
- standard SoC busses like Wishbone or AXI,
- ...

For all other architectures I looked into,
I could not find examples of ascending order for vectors.

My observation is, ascending bit order is rarely used in big-endian architectures,
and not at all used in little-endian architectures and standard system bus definitions.
So I decided not to have an optional ascending order vectors in the TCB specification and implementation.

## References

### [OpenRISC](https://openrisc.io/)

Specification:
- [OpenRISC 1000 ](https://openrisc.io/architecture)

Implementation:
- [mor1kx](https://github.com/openrisc/mor1kx)

### [OpenSPARC](https://www.oracle.com/servers/technologies/opensparc-overview.html)

Specification:
- [OpenSPARC T1 Micro Architecture Specification](https://www.oracle.com/docs/tech/systems/t1-01-opensparct1-micro-arch.pdf) 
- [OpenSPARC T2 Core Microarchitecture Specification](https://www.oracle.com/docs/tech/systems/t2-06-opensparct2-core-microarch.pdf)

Implmentation:
- [OpenSPARC hardware design and verification](http://download.oracle.com/technetwork/systems/opensparc/OpenSPARCT1.1.7.tar.bz2)
- [OpenSPARC T2 Processor Chip Design and Verification](http://download.oracle.com/technetwork/systems/opensparc/OpenSPARCT2.1.3.tar.bz2)

### [OpenPOWER](https://openpowerfoundation.org/)

Specification:
- [Power ISA version 3.1b](https://openpowerfoundation.org/specifications/isa/)

Implementation:
- [Microwatt](https://git.openpower.foundation/cores/microwatt)
- [A2O](https://github.com/OpenPOWERFoundation/a2o)
- [A2I](https://github.com/OpenPOWERFoundation/a2i)