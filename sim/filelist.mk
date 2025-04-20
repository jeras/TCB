################################################################################
# HDL source files
################################################################################

# HDL path
PATH_HDL=../../hdl

# SystemVerilog interface
RTL+=${PATH_HDL}/rtl/tcb_pkg.sv
RTL+=${PATH_HDL}/rtl/tcb_if.sv
# LIBrary
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_passthrough.sv
#RTL+=${PATH_HDL}/rtl/lib/tcb_lib_register_request.sv
#RTL+=${PATH_HDL}/rtl/lib/tcb_lib_register_response.sv
#RTL+=${PATH_HDL}/rtl/lib/tcb_lib_register_backpressure.sv
#RTL+=${PATH_HDL}/rtl/lib/tcb_lib_arbiter.sv
#RTL+=${PATH_HDL}/rtl/lib/tcb_lib_multiplexer.sv
#RTL+=${PATH_HDL}/rtl/lib/tcb_lib_decoder.sv
#RTL+=${PATH_HDL}/rtl/lib/tcb_lib_demultiplexer.sv
#RTL+=${PATH_HDL}/rtl/lib/tcb_lib_error.sv
#RTL+=${PATH_HDL}/rtl/lib/tcb_lib_converter.sv
# GPIO RTL
#RTL+=${PATH_HDL}/rtl/gpio/tcb_gpio.sv
# UART RTL
#RTL+=${PATH_HDL}/rtl/uart/tcb_uart_ser.sv
#RTL+=${PATH_HDL}/rtl/uart/tcb_uart_des.sv
#RTL+=${PATH_HDL}/rtl/uart/tcb_uart_fifo.sv
#RTL+=${PATH_HDL}/rtl/uart/tcb_uart.sv

# SystemVerilog VIP
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_pkg.sv
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_memory.sv
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_tb.sv
# LIBrary
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_passthrough_tb.sv
#TBN+=${PATH_HDL}/tbn/lib/tcb_lib_register_request_tb.sv
#TBN+=${PATH_HDL}/tbn/lib/tcb_lib_register_response_tb.sv
#TBN+=${PATH_HDL}/tbn/lib/tcb_lib_register_backpressure_tb.sv
#TBN+=${PATH_HDL}/tbn/lib/tcb_lib_multiplexer_tb.sv
#TBN+=${PATH_HDL}/tbn/lib/tcb_lib_demultiplexer_tb.sv
#TBN+=${PATH_HDL}/tbn/lib/tcb_lib_converter_tb.sv
## GPIO testbench
#TBN+=${PATH_HDL}/tbn/gpio/tcb_gpio_tb.sv
## UART testbench
#TBN+=${PATH_HDL}/tbn/uart/uart_model.sv
#TBN+=${PATH_HDL}/tbn/uart/uart_model_tb.sv
#TBN+=${PATH_HDL}/tbn/uart/tcb_uart_tb.sv

# combined HDL sources
HDL =${RTL}
HDL+=${TBN}
