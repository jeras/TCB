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
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_register_request.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_register_response.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_register_backpressure.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_error.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_arbiter.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_multiplexer.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_decoder.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_demultiplexer.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_logsize2byteena.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_misaligned_memory_controller.sv
# GPIO RTL
#RTL+=${PATH_HDL}/rtl/peri/gpio/tcb_gpio.sv
# UART RTL
#RTL+=${PATH_HDL}/rtl/peri/uart/tcb_uart_ser.sv
#RTL+=${PATH_HDL}/rtl/peri/uart/tcb_uart_des.sv
#RTL+=${PATH_HDL}/rtl/peri/uart/tcb_uart_fifo.sv
#RTL+=${PATH_HDL}/rtl/peri/uart/tcb_uart.sv

# SystemVerilog VIP
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_transfer_pkg.sv
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_transaction_pkg.sv
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_nonblocking_pkg.sv
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_blocking_pkg.sv
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_protocol_checker.sv
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_memory.sv
#TBN+=${PATH_HDL}/tbn/vip/tcb_vip_tb.sv
# LIBrary
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_passthrough_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_register_request_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_register_response_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_register_backpressure_tb.sv
#TBN+=${PATH_HDL}/tbn/lib/tcb_lib_error_tb.sv
#TBN+=${PATH_HDL}/tbn/lib/tcb_lib_arbiter_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_multiplexer_tb.sv
#TBN+=${PATH_HDL}/tbn/lib/tcb_lib_decoder_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_demultiplexer_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_logsize2byteena_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_misaligned_memory_controller_tb.sv
# SRAM model
TBN+=${PATH_HDL}/tbn/peri/sram/sram_model.sv
## GPIO testbench
#TBN+=${PATH_HDL}/tbn/peri/gpio/tcb_gpio_tb.sv
## UART testbench
#TBN+=${PATH_HDL}/tbn/peri/uart/uart_model.sv
#TBN+=${PATH_HDL}/tbn/peri/uart/uart_model_tb.sv
#TBN+=${PATH_HDL}/tbn/peri/uart/tcb_uart_tb.sv

# combined HDL sources
HDL =${RTL}
HDL+=${TBN}
