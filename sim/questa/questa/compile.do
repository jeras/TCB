vlib questa_lib/work
vlib questa_lib/msim

vlib questa_lib/msim/xpm
vlib questa_lib/msim/xil_defaultlib

vmap xpm questa_lib/msim/xpm
vmap xil_defaultlib questa_lib/msim/xil_defaultlib

vlog -work xpm -64 -incr -mfcu  -sv \
"/tools/Xilinx/Vivado/2023.1/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv" \

vcom -work xpm -64 -93  \
"/tools/Xilinx/Vivado/2023.1/data/ip/xpm/xpm_VCOMP.vhd" \

vlog -work xil_defaultlib -64 -incr -mfcu  -sv \
"../../../hdl/rtl/tcb_pkg.sv" \
"../../../hdl/rtl/tcb_if.sv" \
"../../../hdl/rtl/peri/uart/tcb_uart_des.sv" \
"../../../hdl/rtl/peri/uart/tcb_uart_fifo.sv" \
"../../../hdl/rtl/peri/uart/tcb_uart_ser.sv" \
"../../../hdl/rtl/peri/uart/tcb_cmn_uart.sv" \
"../../../hdl/rtl/peri/gpio/tcb_cmn_gpio.sv" \
"../../../hdl/tbn/vip/tcb_vip_pkg.sv" \
"../../../hdl/tbn/peri/uart/tcb_uart_tb.sv" \
"../../../hdl/tbn/peri/uart/uart_model_tb.sv" \
"../../../hdl/tbn/peri/uart/uart_model.sv" \
"../../../hdl/tbn/vip/tcb_vip_tb.sv" \
"../../../hdl/tbn/peri/gpio/tcb_gpio_tb.sv" \
"../../../hdl/rtl/lib/tcb_lib_converter.sv" \
"../../../hdl/rtl/lib/tcb_lib_passthrough.sv" \
"../../../hdl/rtl/lib/tcb_lib_register_request.sv" \
"../../../hdl/rtl/lib/tcb_lib_common2independent.sv" \
"../../../hdl/rtl/peri/uart/tcb_ind_uart.sv" \
"../../../hdl/rtl/peri/gpio/tcb_ind_gpio.sv" \
"../../../hdl/tbn/vip/tcb_vip_mem.sv" \
"../../../hdl/tbn/lib/tcb_lib_converter_tb.sv" \
"../../../hdl/tbn/lib/tcb_lib_passthrough_tb.sv" \

vlog -work xil_defaultlib \
"glbl.v"

