# Implementation recommendations

The aim of this recommendations is to optimize
Power, Performance, and Area (PPA).

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

## Generic example peripheral

The recommendations will be based on a generic example peripheral
containing some memory mapped registers common in many peripherals.

## Configuration

Confiuration registers are quasi-static,
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
others might use the same address 

| reg. type | writable | readable | sizable | volatile | quasi-static | toggling frequently |
|-----------|----------|----------|---------|----------|--------------|---------------------|
| configuration

## Trivial implementation

```SystemVerilog
module device (
    // TCB-lite subordinate interface
    tcb_lite_if.sub tcb_sub,
    // generic I/O signals
    output logic [32-1:0] dev_config,
    output logic [32-1:0] dev_control,
    input  logic [32-1:0] dev_status,
    output logic [32-1:0] dev_timer,
    output logic [32-1:0] dev_data_out,
    input  logic [32-1:0] dev_data_in
    output logic [32-1:0] dev_fifo_out,
    input  logic [32-1:0] dev_fifo_in
);
```

## Optimizations