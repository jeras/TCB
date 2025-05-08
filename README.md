WARNING: this project is in an ALPHA stage, not advertized yet.
It might already be worth looking at,
but the progress status statements are not reliable,
and the API-s are not stable yet.

DOC + LIB + VIP + PERI

# TCB

This project provides the following parts:
- Tightly Coupled Bus [documentation](doc/TCB.adoc),
- reference interconnect library,
- reference verification library (VIP),
- reference peripherals.


The purpose of TCB is to fill a niche for a low complexity system bus
without unnecessary limitations on throughput.

## Implementation status

| status | description |
|--------|-------------|
| planed | The component should be a part of project, but there is no implementation yet. |
| VIP    | (Work In Progress) The implementation is partially done, or it might require  

### Common shared code

The interface and package are shared across the RTL and verification code
for the rest of the code.

| module                          | status | description |
|---------------------------------|--------|-------------|
| [`tcb_if` ](hdl/rtl/tcb_if.sv ) | done   | SystemVerilog interface. |
| [`tcb_pkg`](hdl/rtl/tcb_pkg.sv) | done   | SystemVerilog package. |

### VIP (Verification IP)

| module                                           | status | description |
|--------------------------------------------------|--------|-------------|
| [`tcb_vip_pkg`](hdl/tbn/vip/tcb_vip_pkg.sv)      | VIP    | Package containing manager/monitor/subordinate code. |
| [`tcb_vip_memory`](hdl/tbn/vip/tcb_if_memory.sv) | VIP    | Multi port memory model. |
| [`tcb_vip_tb` ](hdl/tbn/vip/tcb_vip_tb.sv )      | VIP    | Testbench for core VIP functionality. |

### Reference implementation library

| module                                                          | status | description |
|-----------------------------------------------------------------|--------|-------------|
| [`tcb_lib_passthrough`  ](hdl/rtl/lib/tcb_lib_pasthrough.sv   ) | done   | Trivial passthrough. |
| [`tcb_lib_register`     ](hdl/rtl/lib/tcb_lib_register.sv     ) | planed | Register for request/response paths. |
| [`tcb_lib_connector`    ](hdl/rtl/lib/tcb_lib_conector.sv     ) | planed | Interface connector with automatic handling of parameter differences. |
| [`tcb_lib_arbiter`      ](hdl/rtl/lib/tcb_lib_arbiter.sv      ) | done   | Priority arbiter. |
| [`tcb_lib_multiplexer`  ](hdl/rtl/lib/tcb_lib_multipleser.sv  ) | done   | Multiplexer of multiple managers. |
| [`tcb_lib_decoder`      ](hdl/rtl/lib/tcb_lib_decoder.sv      ) | done   | Address decoder. |
| [`tcb_lib_demultiplexer`](hdl/rtl/lib/tcb_lib_demultiplexer.sv) | done   | Demultiplexer of multiple subordinates. |
| [`tcb_lib_error`        ](hdl/rtl/lib/tcb_lib_error.sv        ) | done   | Error response leaf subordinate. |

### Peripherals

| module                                  | status | description |
|-----------------------------------------|--------|-------------|
| [`tcb_gpio` ](hdl/rtl/gpio/tcb_gpio.sv) | WIP    | GPIO controller. |
| [`tcb_uart` ](hdl/rtl/uart/tcb_uart.sv) | WIP    | UART controller. |

## References

1. QMEM [specification](https://somuch.guru/2016/06/28/qsoc-the-qmem-bus/) and [IP](https://github.com/rkrajnc/or1200-qmem)
1. [Open Core Protocol on Wikipedia](https://en.wikipedia.org/wiki/Open_Core_Protocol)
1. CoreConnect from IBM on Wikipedia](https://web.archive.org/web/20090129183058/http://www-01.ibm.com/chips/techlib/techlib.nsf/products/CoreConnect_Bus_Architecture)
1. [Ibex RISC-V core load/store bus interface](https://ibex-core.readthedocs.io/en/latest/02_user/integration.html)
1. [NeoRV32 RISC-V core bus interface](https://stnolting.github.io/neorv32/#_bus_interface)
1. [AMBA on Wikipedia](https://en.wikipedia.org/wiki/Advanced_Microcontroller_Bus_Architecture)
1. [AMBA on ARM](https://developer.arm.com/Architectures/AMBA)
1. [Wishbone B4](https://cdn.opencores.org/downloads/wbspec_b4.pdf)
1. Pulp Platform Snitch [Reqrsp Interface](https://pulp-platform.github.io/snitch/rm/reqrsp_interface/)
1. OpenHW Group [OBI](https://github.com/openhwgroup/obi) (OpenBus Interface)
1. TileLink [1.8.0](https://github.com/chipsalliance/omnixtend/blob/c192bb6862846a24535b3808dc2f8612d44f2ff8/OmniXtend-1.0.3/spec/TileLink-1.8.0.pdf),
[1.8.1](https://starfivetech.com/uploads/tilelink_spec_1.8.1.pdf)
1. OpenTitan [TileLink IP](https://docs.opentitan.org/hw/ip/tlul/doc/)
