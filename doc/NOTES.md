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
PCK