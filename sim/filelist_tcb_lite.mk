################################################################################
# HDL source files
################################################################################

# HDL path
PATH_HDL=../../hdl

# SystemVerilog interface
#RTL+=${PATH_HDL}/rtl/tcb_pkg.sv
RTL+=${PATH_HDL}/rtl/tcb_lite_if.sv
# LIBrary
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_passthrough.sv
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_register_request.sv
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_register_response.sv
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_register_backpressure.sv
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_error.sv
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_arbiter.sv
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_multiplexer.sv
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_decoder.sv
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_demultiplexer.sv
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_logsize2byteena.sv
RTL+=${PATH_HDL}/rtl/lite_lib/tcb_lite_lib_misaligned_memory_controller.sv
## GPIO RTL
#RTL+=${PATH_HDL}/rtl/peri_lite/gpio/tcb_lite_peri_gpio.sv
## UART RTL
#RTL+=${PATH_HDL}/rtl/peri/uart/tcb_peri_uart_ser.sv
#RTL+=${PATH_HDL}/rtl/peri/uart/tcb_peri_uart_des.sv
#RTL+=${PATH_HDL}/rtl/peri/uart/tcb_peri_uart_fifo.sv
#RTL+=${PATH_HDL}/rtl/peri/uart/tcb_peri_uart.sv

# SystemVerilog VIP
TBN+=${PATH_HDL}/tbn/lite_vip/tcb_lite_vip_manager.sv
TBN+=${PATH_HDL}/tbn/lite_vip/tcb_lite_vip_protocol_checker.sv
TBN+=${PATH_HDL}/tbn/lite_vip/tcb_lite_vip_subordinate.sv
TBN+=${PATH_HDL}/tbn/lite_vip/tcb_lite_vip_memory.sv
TBN+=${PATH_HDL}/tbn/lite_vip/tcb_lite_vip_tb.sv
# LIBrary
TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_passthrough_tb.sv
TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_register_request_tb.sv
TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_register_response_tb.sv
TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_register_backpressure_tb.sv
#TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_error_tb.sv
#TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_arbiter_tb.sv
TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_multiplexer_tb.sv
#TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_decoder_tb.sv
TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_demultiplexer_tb.sv
TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_logsize2byteena_tb.sv
TBN+=${PATH_HDL}/tbn/lite_lib/tcb_lite_lib_misaligned_memory_controller_tb.sv
# RAM models
TBN+=${PATH_HDL}/tbn/peri/sram/sram_model.sv
TBN+=${PATH_HDL}/tbn/peri/cram/cram_model.sv
## GPIO testbench
#TBN+=${PATH_HDL}/tbn/peri/gpio/tcb_peri_gpio_tb.sv
## UART testbench
#TBN+=${PATH_HDL}/tbn/peri/uart/uart_model.sv
#TBN+=${PATH_HDL}/tbn/peri/uart/uart_model_tb.sv
#TBN+=${PATH_HDL}/tbn/peri/uart/tcb_peri_uart_tb.sv

# combined HDL sources
HDL =${RTL}
HDL+=${TBN}
