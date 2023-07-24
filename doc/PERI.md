# Peripherals

## RISC-V related recommendations

### Address bus

Use as few address bits as possible,
all of them on the LSB side.
Due to carry propagation in an adder,
MSB bits take longer to calculate.

### Data bus

#### RISC-V immediate instructions

#### RISC-V extension 64-bit load/store on RV32

#### Configuration registers

#### Control/Status registers

#### Data registers

FIFO
1. reference mode fixed address variable transfer size
2. 2 locations to allow missalligned accesses to the same address
3. mapping the entire buffer into memory twice