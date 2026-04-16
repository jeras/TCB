# Subordinate implementation considerations

The aim of this recommendations is to optimize
Power, Performance, and Area (PPA) for subordinate implementations.

1. Power:
   - minimize toggling, with some focus on high fanout signals,
   - take advantage of smaller transfer size options,
   - minimize power consumption effects crossing write and read logic boundary.
2. Performance (timing):
   - minimize setup time for request signals,
   - minimize clock to output time for response signals.
3. Area:
   - compromise between shared and split resources (address and control registers),
   - take advantage of partial decoding of the address space,
     additionally taking into account the transfer size.

## Response delay and memory ordering

There are a few different ways how to implement subordinates
with typical response delays (0, 1, 2) so that accesses
to memory-mapped I/O registers is properly ordered.

The ordering requirements for a simple register (non-volatile, no side effects) are:
1. every read reflects the value last written into the register,
2. for read modify write transactions, the read must reflect the value before the write.

### Write access

The following write access implementations will be analyzed:
1. write on transfer,
2. write after transfer (`1` clock cycle delay).

WHile an even larger delay between write transfer and register change
can have practical applications, this would be outside the scope of this document.

#### Write on transfer

Write data is written into the addressed register
at the rising clock edge during the handshake transfer cycle.

```SystemVerilog
assign rsp.rdt = reg[req_adr];
```

![Write on transfer block diagram](subordinate_write_on_transfer_block.svg)

![Write on transfer timing diagram](subordinate_write_on_transfer_timing.svg)

#### Write after transfer

The request is registered and thus delayed by one clock cycle compared to the handshake transfer.
Write data is written into the addressed register
at the rising clock edge one clock period after the handshake transfer cycle.

```SystemVerilog
always
assign rsp.rdt = reg[req_adr];
```

![Write after transfer block diagram](subordinate_write_after_transfer_block.svg)

![Write after transfer timing diagram](subordinate_write_after_transfer_timing.svg)

### Read access

The following read access implementations will be analyzed:
1. combinational read,
2. registered request read,
3. registered response read,
4. registered request and response read.

#### Combinational read

The read data multiplexer is driven directly (combinationally) from the request address.

```SystemVerilog
assign rsp.rdt = reg[req.adr];
```

![Combinational read block diagram](subordinate_read_combinational_block.svg)

![Combinational read timing diagram](subordinate_read_combinational_timing.svg)

#### Registered request read

The request address is delayed one clock cycle using a register.
While the address register can be registered unconditionally,
enabling it only during read transfers prevents undesired toggling
from propagating from the request address to read response data.

```SystemVerilog
always @(posedge clk, posedge rst)
if (rst)                      dly_adr <= '0;
else if (vld & rdy & req.ren) dly_adr <= req_adr;

assign rsp.rdt = reg[dly_adr];
```

![Registered request read block diagram](subordinate_read_registered_request_block.svg)

![Registered request read timing diagram](subordinate_read_registered_request_timing.svg)

#### Registered response read

The read response data is delayed one clock cycle using a register.
While the data register can be registered unconditionally,
enabling it only during read transfers prevents undesired toggling
from propagating from a volatile register to read response data.

```SystemVerilog
always @(posedge clk, posedge rst)
if (rst)                      rsp.rdt <= '0;
else if (vld & rdy & req.ren) rsp.rdt <= reg[req.adr];
```

![Registered response read block diagram](subordinate_read_registered_response_block.svg)

![Registered response read timing diagram](subordinate_read_registered_response_timing.svg)

#### Registered request and response read

Both the request address and read response data are registered,
resulting in a delay of 2 clock cycles.

```SystemVerilog
always @(posedge clk, posedge rst)
if (rst) dly_ren <= '0;
else     dly_ren <= vld & rdy & req.ren;

always @(posedge clk, posedge rst)
if (rst)                      dly_adr <= '0;
else if (vld & rdy & req.ren) dly_adr <= req_adr;

always @(posedge clk, posedge rst)
if (rst)          rsp.rdt <= '0;
else if (dly_ren) rsp.rdt <= reg[dly_adr];
```

![Registered request and response read block diagram](subordinate_read_registered_request_and_response_block.svg)

![Registered request and response read timing diagram](subordinate_read_registered_request_and_response_timing.svg)

### Combining read and write access

Not all combination of the above read and write access implementations
will result in an implementation that has a desired response delay and
complies with the desired memory ordering.

#### Response delay 0 (`DLY=0`)

The smallest possible response delay is `0`.

The only possible read/write access combination is
**write on transfer** and **combinational read**.

This combination also allows read modify write to be done in a single clock cycle.

Zero delay implementations can be wrapped into modules providing
request registers (read/write address, write data) or/and
response registers (read data) to achieve larger response delays.

#### Response delay 1 (`DLY=1`)

Response delay of `1` is typical of SRAM memories.

The possible read/write access combination are:
1. **write on transfer** and **registered request read**,
2. **write on transfer** and **registered response read**,
3. **write after transfer** and **registered request read**.

The combination _write on transfer_ and _registered request read_
requires the fewest registers (low ASIC area),
and is therefore a rather common implementation.

The combination _write on transfer_ and _registered response read_
can be used where the system bus is not sensitive to subordinate setup time,
and instead a low clock to response data output delay is desired.
This is probably an uncommon implementation.

The combination _write after transfer_ and _registered request read_
offers a low request setup time, and would be preferred for TCB implementations.

The missing combination _write after transfer_ and _registered response read_
would not meet the memory ordering requirement.
A register read following immediately (without backpressure) after a write to the same register,
would get a response with the old value of the register (before the last write).

#### Response delay 2 (`DLY=2`)

An example of response delay of `2` would be a SRAM with an additional read data register.

The only possible read/write access combination is
**write after transfer** and **registered request and response read**.
This combination provides low setup time and low clock to response data output delay.

## Memory-mapped I/O register types

The recommendations will be based on a generic example peripheral
containing some memory mapped registers common in many peripherals.

| reg. type     | writable | readable | sizable | volatile | quasi-static | toggling frequently |
|---------------|----------|----------|---------|----------|--------------|---------------------|
| configuration | yes      | usually  | no      | no       | yes          | no                  |
| control       | yes      | no       | no      | no       | no           | no                  |
| status        | no       | yes      | no      | yes      | no           | no                  |
| timer/counter | no       | yes      | no      | yes      | no           | yes                 |
| data output   | yes      | usually  | no      | no       | no           | possibly            |
| data input    | no       | yes      | no      | yes      | no           | possibly            |
| FIFO write    | yes      | no       | yes     | no       | no           | no                  |
| FIFO read     | no       | yes      | yes     | yes      | no           | no                  |

## Configuration

Configuration registers are quasi-static,
meaning they are rarely written to,
usually only while the peripheral FSM are in an idle state.

Reading a configuration is rarely useful,
since the SW driver is already aware of the contents.

A typical example would be UART baudrate.

## Control and status

Control registers are typically used to initiate
a transition of a FSM from the IDLE state.
Status registers are used to check (polling) whether a FSM
has finished processing and is back in the IDLE state.

Control registers are usually write-only and
Status registers are usually read-only,
but it is common for them to share the same address,
thus resulting in a combined control status register.

A typical example would be SPI/I2C/1-wire peripherals,
where the control signal starts the FSM initiating a data transaction.
and the status signal is used to check whether the transaction has completed.

Access frequency depends on how long it takes
for the transaction FSM to complete (depends on data rate and packet size).
Status register access frequency further depends on whether the peripheral
uses interrupts or it relies on polling.
Use of DMA to handle large packets can further reduce access frequency.

## Timer and counter

Timer and counter registers show the state of a timer or counter.
For the purpose of this example we assume the values change
approximately at the same rate as the system clock.

While some implementations would have read-only access,
others might use the same address to load the timer or counter value.

A typical example would be a high precision timer or a performance counter.

## Data input/output

Output registers are usually read/write,
but if software does not use read modify write to modify them,
they can be read only.

Input registers are read-only and volatile.

A typical example would be GPIO output, output enable and input registers.

## FIFO write/read

Similar to data input/output registers,
but they are generally accessed in packet bursts.

During an access burst they can have high activity,
but otherwise FIFO read registers only change
when data is loaded into an empty register.

## Generic example peripheral

The example peripheral is written to match the TCB-Lite protocol
with `DLY=1` and a registered request (to minimize request setup time).

### Recommended implementation

A few notes:
- the entire request is registered thus minimizing request setup time,
- there are separate registers fro write and read address and enable signals,
- write and read access are only partially decoded, and no address decoder error is returned,
- the read response data only toggles once on a read (not accounting for glitches),
  except for reads from volatile registers,
  which are masked to zero after the read delay slot.

```SystemVerilog
module device (
    // TCB-lite subordinate interface
    tcb_lite_if.sub tcb,
    // generic I/O signals
    output logic [32-1:0] dev_config,
    output logic [32-1:0] dev_control,
    input  logic [32-1:0] dev_status,
    output logic [32-1:0] dev_timer,
    output logic [32-1:0] dev_data_out,
    input  logic [32-1:0] dev_data_in,
    output logic [32-1:0] dev_fifo_wr,
    input  logic [32-1:0] dev_fifo_rd
);
    logic                       dly_wen;
    logic                       dly_ren;
    logic [tcb.CFG.BUS.ADR-1:0] dly_adr_w;
    logic [tcb.CFG.BUS.ADR-1:0] dly_adr_r;
    logic [tcb.CFG.BUS.SIZ-1:0] dly_siz;
    logic [tcb.CFG.BUS.DAT-1:0] dly_wdt;

    // NOTE: tcb.trn = tcb.vld & tcb.rdy

    // request registers with reset
    always @(posedge tcb.clk, posedge tcb.rst)
    if (rst) begin
        dly_wen <= 1'b0;
        dly_ren <= 1'b0;
        dly_adr_w <= '0;
        dly_adr_r <= '0;
        dly_siz <= '0;
    end else begin
        dly_wen <= tcb.trn & tcb.req.wen;
        dly_ren <= tcb.trn & tcb.req.ren;
        if (tcb.trn) begin
            if (tcb.req.wen)  dly_adr_w <= tcb.req.adr;
            if (tcb.req.ren)  dly_adr_r <= tcb.req.adr;
            dly_siz <= tcb_req_siz;
        end
    end

    // request registers without reset
    always @(posedge tcb.clk, posedge tcb.rst)
    if (tcb.trn & tcb.req.wdt)  dly_wdt <= tcb.req.wdt;

    // write access
    always_ff @(posedge tcb.clk, posedge tcb.rst)
    if (rst) begin
        dev_config   <= '0;
        dev_control  <= '0;
    //  dev_status   <= '0;
        dev_timer    <= '0;
        dev_data_out <= '0;
    //  dev_data_in  <= '0;
        dev_fifo_wr  <= '0;
    //  dev_fifo_rd  <= '0;
    end else begin
        if (dly_wen) begin
            case (dly_adr_w[4:2])
                'd0:  dev_config   <= dly_wdt;
                'd1:  dev_control  <= dly_wdt;
            //  'd2:  dev_status   <= dly_wdt;
                'd3:  dev_timer    <= dly_wdt;
                'd4:  dev_data_out <= dly_wdt;
            //  'd5:  dev_data_in  <= dly_wdt;
                'd6:  dev_fifo_wr  <= dly_wdt;
            //  'd7:  dev_fifo_rd  <= dly_wdt;
            endcase
        end
    end

    // read access
    always_comb
    case (dly_adr_r[4-1:2])
        'd0:  tcb.rsp.rdt <=           dev_config       ;
        'd1:  tcb.rsp.rdt <=           dev_control      ;
        'd2:  tcb.rsp.rdt <=           dev_status       ;
        'd3:  tcb.rsp.rdt <= dly_ren ? dev_timer    : '0;
        'd4:  tcb.rsp.rdt <=           dev_data_out     ;
        'd5:  tcb.rsp.rdt <= dly_ren ? dev_data_in  : '0;
        'd6:  tcb.rsp.rdt <=           dev_fifo_wr      ;
        'd7:  tcb.rsp.rdt <=           dev_fifo_rd      ;
        default: tcb.rsp.rdt <= 'x;
    endcase

    // error response
    always_ff @(posedge tcb.clk, posedge tcb.rst)
    if (rst)  tcb.rsp.err <= 1'b0;
    else      tcb.rsp.err <= 1'b0;

endmodule: device 
```

### PPA optimizations and compromises

**WARNING: while I have experience with implementing clock gate/enable
on signal data paths I do not have much experience with AND gate masking
and signals glitching due to race conditions and carry chain propagation.
This means my recommendations on the first are reliable while on the second much less so.**

Some optimizations result in gains on all three PPA categories,
power, performance (timing) and area.
The basic idea is that fewer logic takes less area, consumes less power
and takes less time to propagate through.

After going through the all obvious optimizations,
what remains requires compromise and measurements
to check if the changes resulted in achieving the desired gains
or maybe the opposite.

Some PPA optimizations can affect software flexibility.
Partial address decoders and lack of decoder error responses
provide PPA gains, but they require more warnings in the documentation,
and make it more difficult to debug SW driver issues.

This document is somehow focused on **dynamic power consumption**,
since this is the less known of the three PPA categories.

The main sources of dynamic power consumption and typical solutions are:
1. Logic in general, less logic means less power.
2. Signal toggling, gates consume dynamic power while charging discharging their capacitive load.
   Reducing toggling and reducing the capacitive load reduces dynamic power consumption.
   1. Data toggling would be toggling due to data value changes in each clock period.
      The following approaches can be used to reduce data toggling:
      - Clock gating can be used to prevent toggling propagation
        through a register stage and also reduces the clock tree power consumption.
      - Using FlipFlops with clock enable is less efficient than clock gating,
        but also easier to implement (a multiplexer at the FF D input
        switching between new input and feedback from FF Q output).
      - Latches. TODO: learn more about using latches.
      - Data masking with AND/OR gates.
   2. Glitches caused by [race conditions](https://en.wikipedia.org/wiki/Race_condition)
      and things like slow carry propagation through a carry chain adder.
      TODO: find and read some articles.
3. Stronger (also faster) gates consume more of both static and dynamic power.
   If timing requirements can be relaxed using pipelining and parallelization,
   weaker gates can be used thus reducing power consumption.
4. High fan-out signals (control logic) have a large capacitive load
   thus affecting both timing and power.

#### Data path registers versus masking

Registers (pipeline stages) using clock gating/enable are efficient
at preventing data toggling propagation, but they introduce clock cycle delay,
and therefore are not always appropriate.
Registers also take a lot of chip area and consume power themselves.

Adding proper clock gating/enable to existing registers is usually the right choice.

Control signals for clock gating, clock enable and AND gate masking
are all high fan-out signals (data vector width),
this might results contrary to expectations.

The most obvious difference between using registers versus masking is that
applying the AND gate mask itself introduces a transition of signals to zero,
this transition than propagates further.
On the other hand removing clock enable does not introduce any transitions.

Consider the following code as example.

```SystemVerilog
logic             enable;
logic [WIDTH-1:0] data_input;
logic [WIDTH-1:0] data_register;
logic [WIDTH-1:0] data_mask;

always_ff @(posedge clk)
if (enable) data_register <= data_input;

assign data_mask = enable ? data_input : '0;
```

![Data path registers versus masking](data_path_registers_versus_masking.svg)

#### Registered request

It is common for system bus implementations to use AND gate masking
for request signals for subordinates that are not currently being addressed.

#### Masking volatile register signals

#### Error response

#### Partial address decoding

#### Partial data decoding (size dependent)

## References

