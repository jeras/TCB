# Peripherals

This section describes various design considerations for TCP peripherals,
with at least some fucus on a RISC-V ISA CPU based SoC.

## RISC-V related considerations

This section attempts to provide considerations for designing
memory mapped peripherals to be used with a RISC-V CPU.
The focus is on instructions containing an immediate,
since those are the source of relevant limitations.

### Load/Store addressing

All RV32I, RV64I and RV128I load/store (`L[BHWDQ]`/`S[BHWDQ]`) operations
use a register for a base address and a 12-bit sign-extended offset immediate.
The two added together create a 4kB window with byte address access granularity.
Since the immediate is signed, half are below and half are above the base address.
The following table provides the address range and number of locations
for available sizes and aligned accesses.

| access type | from       | to         | locations |
|-------------|------------|------------|-----------|
| byte        | `-12'h800` | `+12'h7ff` |      4096 |
| half        | `-12'h800` | `+12'h7fe` |      2048 |
| word        | `-12'h800` | `+12'h7fc` |      1024 |
| double      | `-12'h800` | `+12'h7f8` |       512 |
| quad        | `-12'h800` | `+12'h7f0` |       256 |

Compressed instructions from the C extension load/store (`C.L[WDQ]`/`C.S[WDQ]`) operations
use a register for a base address and a zero-extended 5-bit offset immediate, scaled by the access size.
The two added together create a 4kB window with byte address access granularity.
Since the immediate is zero-extended, all addresses are above the base address.
The following table provides the address range and number of locations
for available sizes and aligned accesses (only the base can be misaligned).

| access type | scale | from     | to       | locations |
|-------------|-------|----------|----------|-----------|
| word        |     4 | `7'h000` | `7'h03c` |        32 |
| double      |     8 | `8'h000` | `8'h0f8` |        32 |
| quad        |    16 | `9'h000` | `5'h1f0` |        32 |

For a common 32-bit peripheral interface with only full width locations,
I base instructions can address 1024 locations and
C extension instructions can address 32 locations.

### Arithmetic/logic operations with immediate operands

RV32/64/128I arithmetic operation `SLTI` (set less than immediate)
has a 12-bit sign-extended immediate.
It can be used for measurement comparisons in the range -2048 to 2047.

RV32/64/128I arithmetic operation `SLTIU` (set less than immediate unsigned)
has a 12-bit zero-extended immediate.
It can be used for measurement or counter comparisons in the range 0 to 4095.

RV32/64/128I logical operations `ANDI`, `ORI`, `XORI` have a 12-bit sign-extended immediate.
The immediate 11 LSB bits `[10:0]` can be used as masks for peripheral registers.
The immediate 12th bit `[11]` is sign extended to full register width `XLEN`,
so it can only be used to mask all bits from MSB to 11 `[MSB:11]` (MSB can be 32/64/128).

### Conditional branches

Instructions `BLT` (branch if less then) and `BGE` (branch if greater or equal)
with comparing against the zero register R0
can be used to branch on the sign of a register value,
or simply the MSB bit of a register.

## Memory mapped register ABI recommendations

This ABI recommendations are intended for peripherals
implemented using memory mapped registers.

Recommendations are focusing on:
- RTL with good timing and low power consumption,
- drivers with few instruction in critical loops.

### Address bus

NOTE: this recommendation is implementation specific.
It makes sense on designs with the focus on low access latency.

Use as few address bits as possible,
all of them on the LSB side.
Due to carry propagation in an adder,
MSB bits take longer to calculate.

This also makes

### Peripheral registers

| type           | writable | readable | volatile | access rate |
|----------------|----------|----------|----------|-------------|
| configuration  | yes      | yes      | no       | low         |
| control        | yes      | no       |          | medium      |
| status         | no       | yes      | yes      | medium      |
| control/status | yes      | yes      | yes      | medium      |
| data tx/write  | yes      | no       |          | high        |
| data rx/read   | no       | yes      | yes      | high        |
| data duplex    | yes      | yes      | yes      | high        |

### Data bus

#### RISC-V immediate instructions

#### RISC-V extension 64-bit load/store on RV32

#### Configuration registers

#### Control/Status registers

#### Data registers

#### Data FIFO

The implementation might depend on the data unit size
which is assumed to be a pawer of two of base unit byte (byte/half/word/double/...).


I propose multiple variants:
1. reference mode fixed address fixed transfer size
1. reference mode fixed address variable transfer size
2. 2 locations to allow misaligned accesses to the same address
3. mapping the entire buffer into memory twice

##### 