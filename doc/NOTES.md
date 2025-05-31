# TCB protocol layers

1. Handshake layer

Also Physical or BUS layer.
Also Transfer layer.

Abbreviation `HSK`.
https://www.abbreviations.com/abbreviation/handshake

2. Bus layer

Also Transaction layer, but AXI terminology is not a good match,
since on AXI a single transaction can/must involve multiple transfers on different channels.

This layer defines signal subsets.

Abbreviation `BUS`.

https://en.wikipedia.org/wiki/Duplex_(telecommunications)

There are two types of duplex communication systems: full-duplex (FDX) and half-duplex (HDX).

3. Protocol layer

Defines restrictions on signal values, what are valid/invalid combinations.
Abbreviation PTC (ProToCol)

Packeting layer
PMA

## Physical Memory Attributes

How to implement a PMA checker

Causes for PMA errors (traps):
- misaligned access,
- access size,
- access offset (offset from alignment to bus width or XLEN),
- execute/read/write access,
- cachability (how this affects memory vs IO)
- coherence (TODO)
- atomicity (implemented in CPU vs implemented in interconnect)
- reservability (no plan to support yet)
- memory ordering (TCB supports only RVTSO)
- idempotency (how speculative access like prefetch affects read/write side effects).

PMAs can be checked during the request phase with the following limitations:
- a custom address decoder for testing PMAs for busses behind a register stage

PMAs can be checked during the response phase based on response errors:
- additional registers would be needed to store the PC, LSU address
