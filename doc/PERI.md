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

Arithmetic operation `SLTI` (set less than immediate)
has a 12-bit sign-extended immediate.
It can be used for measurement comparisons in the range -2048 to 2047.

Arithmetic operation `SLTIU` (set less than immediate unsigned)
has a 12-bit zero-extended immediate.
It can be used for measurement or counter comparisons in the range 0 to 4095.

Logical operations `ANDI`, `ORI`, `XORI` have a 12-bit sign-extended immediate.
The immediate 11 LSB bits `[10:0]` can be used as masks for peripheral registers.
The immediate 12th bit `[11]` is sign extended to full register width `XLEN`,
so it can only be used to mask all bits from MSB to 11 `[MSB:11]`.

### Compressed logic operations with immediate operands

Logical operation `C.ANDI` has a 6-bit sign extended immediate.
The immediate 5 LSB bits `[4:0]` can be used as masks for peripheral registers.
The immediate 6th bit `[5]` is sign extended to full register width `XLEN`,
so it can only be used to mask all bits from MSB to 5 `[MSB:5]`.

### Load immediate instructions

The `LI` pseudo instruction can be used to load
32/18/12/6-bit sign extended constants into a register.
The sign extension means, the MSB bit of the given constant width
is copied to fill the full XLEN register width.
Depending on the constant width
different instruction sequences can be used.
This sequences use the following immediate instructions.
1. `LUI` (load upper immediate) provides a sign extended 20-bit immediate `[31:12]`, LSB 12-bits `[11:0]` are zeroed.
2. `ADDI` (add immediate) provides a sign extended 12-bit immediate `[31:12]`, can be used without `LUI`, if the source register is `x0`.
3. `C.LUI` (compressed load upper immediate) provides a sign extended 6-bit immediate `[17:12]`, LSB 12-bits `[11:0]` are zeroed.
2. `C.LI` (compressed load immediate) provides a sign extended 6-bit immediate `[5:0]`.

| width | instruction sequence | sequence length |
|-------|----------------------|-----------------|
|    32 |   `LUI`, `ADDI`      | 8B              |
|    18 | `C.LUI`, `ADDI`      | 6B              |
|    12 |          `ADDI`      | 4B              |
|     6 | `C.LI`               | 2B              |

TODO: add sequences for 64-bit immediate loads.

### Conditional branches

Instructions `BLT` (branch if less then) and `BGE` (branch if greater or equal)
with comparing against the zero register `x0`
can be used to branch on the sign of a register value,
or simply the MSB bit of a register.

### RISC-V extension 64-bit load/store on RV32

TODO

## Memory mapped register ABI recommendations

This ABI recommendations are intended for
peripherals implemented using memory mapped registers
and the system bus connecting them.

Recommendations are focusing on:
- RTL optimizations for:
  - fast clock timing,
  - low logic utilization and
  - low power consumption,
- drivers with few instruction in critical loops to maximize access rate.

### System bus recommendations

#### Address bus

NOTE: this recommendation is implementation specific.
It makes sense on designs with the focus on low access latency.

Use as few address bits as possible,
all of them on the LSB side.
Due to carry propagation in an adder,
MSB bits take longer to calculate.

A reasonable aim would be to make the address space
of a single peripheral or or group of peripherals
small enough to be addressable with a single pointer register.
A 12-bit address space can be addressed with RISC-V I base instructions.
A 7-bit address space of 32-bit registers can be addressed with RISC-V C extension instructions.

#### Data bus

The most common width for a peripheral data bus is 32-bits,
this is true even in systems with a 64-bit processor.
So it makes sense to recommend a 32-bit bus width for most peripherals.

64-bit wide data busses still make sense in cases,
where the peripheral contains 64-bit wide registers which
require or prefer atomic access.
A few examples would be:
- 64-bit timers/counters,
- TODO.

It is also common to only access peripheral registers
with the full data bus width aligned transfers.
Peripherals can return an error response
in case of a non conforming transfer request.

#### Independent read/write channels

The main potential advantage of independent read/write channels
is to allow for full duplex throughput.
But it only makes sense in case if the peripheral
can take advantage from such throughput.

Another advantage of independent channels is reduced power consumption.
Since the read/write addresses are independent,
it is possible to prevent write accesses from causing toggling in read logic
and conversely.

### Peripheral registers

It is common to describe peripheral registers as being one of the following types.

| type           | writable | readable | volatile | access rate | type        |
|----------------|----------|----------|----------|-------------|-------------|
| configuration  | yes      | yes      | no       | low         | semi static |
| control        | yes      | no       |          | medium      | dynamic     |
| status         | no       | yes      | yes      | medium      | dynamic     |
| control/status | yes      | yes      | yes      | medium      | dynamic     |
| data tx/write  | yes      | no       |          | high        | dynamic     |
| data rx/read   | no       | yes      | yes      | high        | dynamic     |
| data duplex    | yes      | yes      | yes      | high        | dynamic     |

#### Configuration registers

Configuration registers are accessed infrequently.
It is common to write them once at initialization
and to never read from them.
Even if the value of a configuration register is needed in software,
it is common to have a shadow copy in memory for such use cases.

Due to low access rates it usually does not make much sense
to optimize for access rate, and power consumption.
Complex equations can be used to calculate the register values,
or the RISC-V pseudo instruction `LI` can be used to load a constant known at compile time.

It still makes sense to optimize for clock timing and logic utilization,
since it affects the entire design.

One such optimization would be to not implement
read access to configuration registers,
and instead use shadow copies in memory.
This saved the area and delay from read data multiplexers.

#### Control/Status registers

Control registers, status registers and combined control/status registers
access rate depends on whether the peripheral is
designed for polling (high access rate) or is interrupt driven (medium access rate).
In both cases it can be important to minimize the latency.

Primarily control registers are used by drivers
to write to inputs into FSM (finite state machine) implemented in RTL,
while status registers are used to read the outputs from RTL FSM. 

Control register values are often constructed by
combining individual control field constants with `OR` operations.
Status registers values are often interpreted by
sampling individual status fields using masks applied with `AND` operations.
For combined control/status registers, there are also use cases,
where read modify write sequences are used.

Limiting the control/status registers to 12 relevant bits `[11:0]`
with keeping the rest `[31:12]` reserved,
enables the use of RISC-V instructions `ORI` and `ANDI` to perform
construction and masking fast and without consuming temporary RISC-V GPR-s.

Limiting the control/status register to 8 LSB relevant bits
with the rest reserved and using byte load/store instructions,
could reduce power consumption for high access rate registers.

TODO:
- set/clear/toggle on write,
- side effects like clear on read,
- ...

#### Data registers

Handling data could be placed into categories:
1. reading a continuously changing (volatile),
2. writing a value,
3. communication protocol, with full flow control (request driven),
4. communication protocol, without full flow control.

Reading continuously changing (volatile) value
provides a snapshot of the value in time,
values outside the read cycle are ignored.
In such use cases, it is common to have an interrupt
triggered by a category of values or value transitions,
an alternative is periodic polling.
Common examples would be:
- GPIO inputs (switches, buttons),
- timers and counters,
- ADC (sensors: thermometer, power supply voltmeter, ...),
- ...

Writing a value would have the following examples:
- GPIO outputs,
- DAC,
- ...

Bit-banging protocol implementations are a special case,
where GPIO inputs/outputs are used to emulate a protocol.
Some protocol require strict timing (UART RX/TX, 1-wire master, ...),
others don't (SPI master, I2C master, I3C master, JTAG master, ...).

Communication protocols, with full flow control,
are protocol masters where each data transfer
is explicitly requested by the peripheral.
Examples are SPI, I2C, 1-Wire, ...

Communication protocol, without full flow control,
are protocol slaves where the peripheral does not request each data transfer.
The protocol might provide no hardware flow control (SPI, JTAG, Ethernet, ...),
or some form of hardware flow control (UART RTS/CTS, I2C clock extension, ...).
This communication protocols might also provide some form of software flow control,
implemented on a higher OSI level.


4. communication protocol, where all transfers (transmitted and received)
   are driven by the observed peripheral


1. Data registers are used in case where each data transfer
   is requested explicitly by the peripheral, for example:
   Pheripherals where data is constan
2. data FIFO with register access 

Only cases, where data is accessible as a single unit are considered here.
If multiple data units are available for access,
then those are described in the data FIFO section.
This is not a clean cut distinction,
so there are some shared consideration between this and the FIFO section.

Different data unit widths are possible:
- single bit for minimalistic implementations of serial protocols,
- 8-bits for byte oriented communication protocols (UART, I2C, ...),
- timers/counters of any width (8/16/24/32/48/64/...),
- GPIO input/output of any width (1..64, ...).

TODO: side effects.

#### Data FIFO

The implementation might depend on the data unit size
which is assumed to be a power of two of base unit byte (byte/half/word/double/...).



I propose multiple variants:
1. reference mode fixed address single unit transfer size
1. reference mode fixed address variable array of units transfer size
2. 2 locations to allow misaligned accesses to the same address
3. mapping the entire buffer into memory twice

| `MOD` | sizes |
|-------|-------|
| `REF` | unit  |
| `REF` | unit  |
| `MEM` |

##### Reference mode

In TCB reference mode all data is aligned to the LSB side of the register.


