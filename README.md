# TCB

Tightly Coupled Bus [documentation](doc/TCB.md).

The purpose of TCB is to fill a niche for a low complexity system bus
without unnecessary limitations on throughput.

## Implementation status

### VIP

| module                                      | status | description |
|---------------------------------------------|--------|-------------|
| [`tcb_vip_pkg`](hdl/tbn/vip/tcb_vip_pkg.sv) | done   | Package containing shared code. |
| [`tcb_vip_dwc`](hdl/tbn/vip/tcb_vip_dev.sv) | done   | Device model for manager/monitor/subordinate model. |

### Interconnect library

| module                                                          | status | description |
|-----------------------------------------------------------------|--------|-------------|
| [`tcb_if`               ](hdl/rtl/tcb_if.sv                   ) | done   | SystemVerilog interface. |
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

QMEM:
https://somuch.guru/2016/06/28/qsoc-the-qmem-bus/
https://github.com/rkrajnc/or1200-qmem

https://github.com/Wren6991/Hazard3/blob/master/hdl/hazard3_cpu_2port.v
https://en.wikipedia.org/wiki/Open_Core_Protocol
https://web.archive.org/web/20090129183058/http://www-01.ibm.com/chips/techlib/techlib.nsf/products/CoreConnect_Bus_Architecture

## References

1. [Ibex RISC-V core load/store bus interface](https://ibex-core.readthedocs.io/en/latest/02_user/integration.html)
2. [NeoRV32 RISC-V core bus interface](https://stnolting.github.io/neorv32/#_bus_interface)
3. [AMBA4 AHB4](https://developer.arm.com/documentation/ihi0033/latest/)
4. [Wishbone B4](https://cdn.opencores.org/downloads/wbspec_b4.pdf)

https://pulp-platform.github.io/snitch/rm/reqrsp_interface/

### AMBA

https://en.wikipedia.org/wiki/Advanced_Microcontroller_Bus_Architecture

### OBI1

https://github.com/openhwgroup/core-v-docs/tree/master/cores/obi
file:///home/ijeras/Downloads/OBI-v1.4.pdf

### TileLink

https://github.com/chipsalliance/omnixtend/blob/c192bb6862846a24535b3808dc2f8612d44f2ff8/OmniXtend-1.0.3/spec/TileLink-1.8.0.pdf
https://starfivetech.com/uploads/tilelink_spec_1.8.1.pdf

https://docs.opentitan.org/hw/ip/tlul/doc/