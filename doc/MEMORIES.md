# SRAM

This document provides some analysis of FPGA/ASIC SRAM memories.
The focus is on the following aspects affecting TCB compatibility:
1. timing:
   - control, address, write data setup time,
   - read data clock to output time.
2. features and behavior:
   - write byte enable (bit enable),
   - read byte enable and read data bus hold,
   - asynchronous read (typical for LUT based RAM),
   - additional read data register.

## Modeling and inference



## FPGA

Block SRAM on FPGA devices often includes an additional read data register (pipelined mode).
Without this additional register SRAM behavior matches TCB with `DLY=1`,
with this register enabled SRAM behavior matches TCB with `DLY=2`.


| FPGA series                  | delay | **write** byte enable | **read** byte enable | read data bus hold |
|------------------------------|-------|-----------------------|----------------------|--------------------|
| GW1NR BSRAM (bypass)         | 1     | yes                   | no                   | yes                |
| GW1NR BSRAM (pipelined)      | 2     | yes                   | no                   | yes                |
| GW1NR SSRAM (asynchronous)   | 0     | yes                   | not applicable       | not applicable     |

### Xilinx

7 Series FPGAs

link:https://docs.xilinx.com/v/u/en-US/ug473_7Series_Memory_Resources[Memory Resources],

### Altera



### Gowin

NOTE: SRAM functionality like dual port support, byte enable support and LUT RAM availability
can differ between devices withing the same family and between revisions of the same device.

Gowin FPGA memory resources are:
- bloc SRAM (BSRAM):
  - single/semi-dual/dual port,
  - byte enable,
  - bypass read and pipeline read modes (optional output register),
  - normal write and write-through modes,
  - output cascading multiplexer.
- shadow SRAM (SSRAM):
  - single/semi-dual port.

[UG285, Gowin BSRAM & SSRAM User Guide](https://www.gowinsemi.com/upload/database_doc/1785/document/68f69723d7d7d.pdf)
provides information like timing diagrams and instantiation examples for generated primitives.

The documented timing diagrams do not show the BSRAM behavior
when no read is performed (output clock enable `OCEA`/`OCEB` is not active),
so the full read data behavior can't be understood from the documentation alone.

[SUG550, Gowin Synthesis User Guide](https://www.gowinsemi.com/upload/database_doc/1878/document/69b862abe7274.pdf)
provides some inference examples.

Simulation models (Gowin IDE folder `IDE/simlib/gw1n/*`) provide full details on primitive behavior.

| primitive       | mode        | parameters |
|-----------------|-------------|------------|
| `SP`/`SPX9`     | single port | `READ_MODE`, `WRITE_MODE` |
| `DPB`/`DPX9B`   | dual port   | `READ_MODE0/1`, `WRITE_MODE0/1` |
| `SDPB`/`SDPX9B` | semi-dual   | `READ_MODE` |
| `pROM`/`pROMX9` | read-only   | `READ_MODE` |

| primitive                           | mode        |
|-------------------------------------|-------------|
| `RAM16S1`/`RAM16S2`/`RAM16S4`       | single port |
| `RAM16SDP1`/`RAM16SDP2`/`RAM16SDP4` | semi-dual port |
| `ROM16`                             | read-only |

#### GW1NR

The Sipeed [Tang Nano 9k](https://wiki.sipeed.com/hardware/en/tang/Tang-Nano-9K/Nano-9K.html) board
uses a GW1NR-9 device from the Gowin GW1NR[https://www.gowinsemi.com/en/support/database/1781/] series.

[GW1NR series of FPGA Products Data Sheet](https://www.gowinsemi.com/upload/database_doc/1785/document/68f69723d7d7d.pdf)
provides some details on configuration options and series/device/revision specifics.

## ASIC

### SkyWater SKY130 PDK

TODO

### GlobalFoundries GF180MCU PDK

link:https://gf180mcu-pdk.readthedocs.io/en/latest/IPs/SRAM/gf180mcu_fd_ip_sram/cells/gf180mcu_fd_ip_sram__sram512x8m8wm1/gf180mcu_fd_ip_sram__sram512x8m8wm1.html[SRAM macro].

### IHP 130nm BiCMOS Open Source PDK

link:https://github.com/IHP-GmbH/IHP-Open-PDK/tree/main/ihp-sg13g2/libs.ref/sg13g2_sram[SRAM macros]

### OpenRAM

