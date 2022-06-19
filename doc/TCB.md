# Tightly Coupled Bus

Tightly Coupled Bus is a system bus based on FPGA/ASIC synchronous SRAM memory interfaces.

Proposed names are based on:
* Tightly Integrated Memory (TIM) used by [SiFive](https://www.sifive.com/),
* Tightly Coupled Memory (TCM) used by [ARM](https://www.kernel.org/doc/Documentation/arm/tcm.txt),
  [Codasip](https://codasip.com/), and [Syntacore](https://syntacore.com/),
* Local Memory (LM) used by [Andes](http://www.andestech.com/en/risc-v-andes/)

A processor native system bus is usually custom designed
to supports exactly the features that are present in the processor itself.
This also means there are differences between the protocols
used by instruction fetch and load/store unit.

This description will start with a superset of features
at least partially shared by both interfaces.

The design is based on the following principles:
* Intended for closely coupled memories and caches, and therefore based on synchronous memory (SRAM) interfaces.
* Support pipelining for both writes and reads to minimize stalling overhead.
  Meaning the handshake is done during the arbitration phase.
* Handshake based on AXI4 (valid/ready).
* Low power consumption should be considered.

What it is not intended for:
* It is not optimized for clock domain crossing (CDC), which has a large delay between the start of a request and the response, and the delay has some unpredictability.
* Does not provide out of order access functionality.
* It is not a good fit for managers with a variable pipeline length in the load/store unit.

## References

1. [Ibex RISC-V core load/store bus interface](https://ibex-core.readthedocs.io/en/latest/02_user/integration.html)
2. [NeoRV32 RISC-V core bus interface](https://stnolting.github.io/neorv32/#_bus_interface)
3. [AMBA4 AHB4](https://developer.arm.com/documentation/ihi0033/latest/)

## Terminology

TCB terminology is mostly based on Verilog and AMBA.

| Term | Description |
|------|-------------|
| period | The term _clock period_ is preferred over _clock cycle_ to avoid confusion with _access cycle_ which can be multiple clock periods long. |
| manager | Managers are modules driving requests toward a subordinate and receiving a response from it. This term is equivalent to _master_. |
| subordinate | Subordinates are module receiving requests from a manager and responding to it. This term is equivalent to _slave_. |
| handshake | Exchange of `valid` and `ready` signals during between manager and subordinate. |
| cycle | Or _access cycle_ is one or more clock periods long exchange between a master and a subordinate governed by a valid/ready handshake, and it ends with a transfer. TODO: clarify if the delayed response is also part of the access cycle. |
| transfer | Each access cycle ends in a single clock period long transfer where valid and ready handshake signals are both active. |
| request | The collective value of signals (address, write enable, byte enable, write data) driven by a manager toward a subordinate, while valid is active during an access cycle. |
| response |  TODO: clarify whether a response can be held multiple clock periods. |
| backpressure | A subordinate can delay the transfer by driving the ready signal low. |
| back-to-back | Performing transfers continuously in each clock period, without idling the bus by waiting the for a response before issuing e new request. |
| parameter | Static (compile time) configuration of a HDL/RTL module, `parameter` in Verilog or `generic` in VHDL. |
| configuration | 
| control |
| status |

## Bus signals

Regarding naming conventions,
for aesthetic reasons (vertical alignment) all signal names are
[three-letter abbreviation (TLA)](https://en.wikipedia.org/wiki/Three-letter_acronym).
Suffixes specifying the direction of module ports (input/output, i/o) shall be avoided.
Instead the set of signals can have a prefix or is grouped into a SystemVerilog interface.
This set name shall use specifiers like manager/subordinate (master/slave, m/s).

The SRAM signal chip select/enable is replaced with the AXI handshake signal valid `vld`.
Backpressure is supported by adding the AXI handshake signal ready `rdy`.
Handshake signals shall follow the basic principles defined for the AXI family of protocols.
* While valid is not active all other signals shall be ignored (`X` in timing diagrams).
* `vld` must be inactive during reset.
* Once the manager asserts `vld`, it must not remove it till the transfer is completed by an active `rdy` signal.
* The manager must not wait for `rdy` to be asserted before starting a new transfer by asserting `vld`.
* The subordinate can assert/remove the `rdy` signal without restrictions.

This means once a transfer is initiated, it must be completed.
Since `rdy` can be asserted during reset (`rdy` can be a constant value),
`vld` must not be asserted, since this would indicate transfers while in reset state.
Since the subordinate is allowed to wait for `vld` before asserting `rdy` (no restrictions),
the manager can't wait for `rdy` to before asserting `vld`,
since this could result in a lockup.
There is also no integrated timeout abort mechanism,
although it would be possible to place such functionality
into a module placed between the manager and the subordinate.

| parameter/generic | description |
| `AW`              | Address width. |
| `DW`              | Data width. |
| `BW=DW/8`         | Byte select width. |

| signal | width  | direction | description |
|--------|--------|-----------|-------------|
| `vld`  | 1      | M -> S    | Hanshake valid. |
| `wen`  | 1      | M -> S    | Write enable. |
| `adr`  | `AW`   | M -> S    | Address. |
| `ben`  | `DW`/8 | M -> S    | Byte enable (select). |
| `wdt`  | `DW`   | M -> S    | Write data. |
| `rdt`  | `DW`   | S -> M    | Read data. |
| `err`  | 1      | S -> M    | Error response. |
| `rdy`  | 1      | S -> M    | Hanshake ready. |

Various implementations can add custom signals to either the request or response,
some examples of custom signals would be:
* cache related signals,
* multiple types of error responses.

## Handshake protocol and signal timing

### Write transfer

A write transfer is performed when both handshake signals `vld` and `rdy` are simultaneously active
and the write enable signal `wen` is also active.

Only bytes with an active corresponding byte enable bit in `ben` are written.
The other bytes can be optimized to unchanged value, zeros or just undefined,
depending what brings the preferred optimization for area timing, power consumption, ...
The same optimization principle can be applied to all signals when valid is not active.

There are no special pipelining considerations for write transfers,
all signals shall be propagated through a pipeline,
similar to a single direction data stream

The base protocol does not have a mechanism for confirming
write transfers reached their destination and were successfully applied.

[image]

### Read transfer

A read transfer is performed when both handshake signals `vld` and `rdy` are simultaneously active
and the write enable signal `wen` is not active.

The handshake is done during the arbitration phase, it is primarily
about whether the address `adr` from the manager can reach the subordinate.

Read data is available on `rdt` after a fixed delay of 1 clock cycle from the transfer.

## Reference implementation

The reference implementation is written in SystemVerilog.

### RTL components

#### Interface

#### Arbiter

#### Decoder

#### Register

#### Error

The error subordinate `tcb_err` is used to close unused interconnect manager ports.
The most common use case would be to replace a peripheral device disabled with a parameter.

It will provide an error response to any request.
It does not add backpressure.

### Testbench components

NOTE: The testbench code is in an Alpha state.
The aim is for a fully UVM compatible implementation.
The current code just barely covers the documented functionality.

#### Manager

#### Subordinate

## RTL design recommendations

### Parameter validation

### Handling of reset transitions

### Peripherals

The reference TCB implementation is written in SystemVerilog,
therefore this document discusses Verilog parameters.
The VHDL equivalent would be generics,
and other HDL languages also have constructs with equivalent functionality.

| parameter     | type           | default | description |
|---------------|----------------|---------|-------------|
| `DLY`         | `int unsigned` | `'d1`   | Read delay. |
| `CFG_REQ_REG` | `bit`          | `1'b0`  | Configuration: enable REQest REGister. |
| `CFG_RSP_REG` | `bit`          | `1'b1`  | Configuration: enable ReSPonse REGister. |
| `CFG_ENR_CFG` | `bit`          | `1'b1`  | Configuration: ENable Read access to ConFiGuration registers. |

If both address and 

The [GPIO controller](GPIO.md) is a good example how this parameters can be used
to provide the desired area/timing optimizations for a specific design.

In the default configuration read/write data paths behave as follows:
- In the write path the address is not registered and the decoder delay falls on the request side.
- In the read path the address is not registered and the decoder delay falls on the request side.
  Since the read data bus is registered, there is no decoder delay at the response side.
- Since read access to configuration registers is enabled, it affects the timing on the request side.



## Limitations and undefined features

There are some generalizations and additional features that can be implemented,
but were not researched well enough to be fully defined.

### Data output hold

SRAM usually holds the data output from the last read request,
till a new request is processed.
In a similar fashion, the entire bus could hold the last read value,
this means read data multiplexers in decoder modules have to hold.
The held data can be lost if a subordinate is accessed by another manager.

Read data hold can be useful during CPU stalls.
Either there is no need to repeat a read or a temporary buffer
for read data can be avoided.

### Out of order transfers

Out of order reads are not supported.

### Generalized read delay

The delay of 0 would be an asynchronous read,
a delay of 1 is equal to a common SRAM read cycle,
longer delays can be caused by registers in the system bus interconnect.

### Integration with standard system busses

It is possible to translate between the processor native system bus and
standard system busses like APB, AHB, AXI4-Lite, Wishbone, ...

Such translation could compromise the performance,
so it might make sense to implement a standard bus interface unit (BIU)
separately inside the processor core,
instead of attaching translators to the optimized native bus.

### Write confirmation

Write confirmation could be returned with the same timing as read data.

In case the native system bus is only used for the intend purpose
of connecting tightly coupled memories, writes can be assumed to always succeed.

Write through cache access was not yet researched.

### Atomic access

TODO, on some implementations it might be possible
to simultaneously perform both read and write.