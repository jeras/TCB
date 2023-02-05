################################################################################
# tools
################################################################################

VERILATOR?=verilator
VERILATOR_COVERAGE?=verilator_coverage

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
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_arbiter.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_multiplexer.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_decoder.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_demultiplexer.sv
RTL+=${PATH_HDL}/rtl/lib/tcb_lib_error.sv
# GPIO RTL
RTL+=${PATH_HDL}/rtl/gpio/tcb_gpio.sv
# UART RTL
RTL+=${PATH_HDL}/rtl/uart/tcb_uart_ser.sv
RTL+=${PATH_HDL}/rtl/uart/tcb_uart_des.sv
RTL+=${PATH_HDL}/rtl/uart/tcb_uart_fifo.sv
RTL+=${PATH_HDL}/rtl/uart/tcb_uart.sv

# SystemVerilog VIP
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_pkg.sv
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_dev.sv
TBN+=${PATH_HDL}/tbn/vip/tcb_vip_tb.sv
# LIBrary
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_passthrough_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_register_request_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_register_response_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_register_backpressure_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_multiplexer_tb.sv
TBN+=${PATH_HDL}/tbn/lib/tcb_lib_demultiplexer_tb.sv
## GPIO testbench
TBN+=${PATH_HDL}/tbn/gpio/tcb_gpio_tb.sv
## UART testbench
TBN+=${PATH_HDL}/tbn/uart/uart_model.sv
TBN+=${PATH_HDL}/tbn/uart/uart_model_tb.sv
TBN+=${PATH_HDL}/tbn/uart/tcb_uart_tb.sv

# combined HDL sources
HDL =${RTL}
HDL+=${TBN}

# top level file
TOP ?= tcb_tb

################################################################################
# Verilator compiler/linker flags
################################################################################

# Generate binary executable
VFLAGS += --binary
# Optimize
VFLAGS += -O3
# Number of CPU threads
VFLAGS += -j 0

# specify SystemVerilog LRM version
#VFLAGS += +1800-2012ext+sv
# set defailt timescale
VFLAGS += --timescale 1ps/1ps
#VFLAGS += --timescale-override 1ps/1ps
# optimize for speed or maximize finding X assign issues
VFLAGS += --x-assign fast
#VFLAGS += --x-assign 0
#VFLAGS += --x-assign 1
#VFLAGS += --x-assign unique
# Warn about lint issues; may not want this on less solid designs
#VFLAGS += -Wall
# Disable warnings
VFLAGS += -Wno-INITIALDLY

# Check SystemVerilog assertions
VFLAGS += --assert
# Generate coverage analysis
#VFLAGS += --coverage

# Run Verilator in debug mode
#VFLAGS += --debug
# Add this trace to get a backtrace in gdb
#VFLAGS += --gdbbt

# Make waveforms
#ifdef TRACE
#VFLAGS += --trace
VFLAGS += --trace-fst
VFLAGS += --trace-structs
#endif

################################################################################
# Verilog macros
################################################################################

# set VERILATOR macro (used to handle tool quirks)
#MCR += -DVERILATOR
ifdef TRACE
MCR += -DTRACE_DEBUG
endif

################################################################################
# Verilog toplevel parameter override
################################################################################

# TCB address/data bus widths
ABW ?= 32
DBW ?= 32
# TCB response delay
DLY ?= 1

PAR += -GABW=${ABW}
PAR += -GDBW=${DBW}
#PAR += -GDLY=${DLY}

################################################################################
# Verilog $plusargs runtime arguments
################################################################################

#ARG += +FILE_MEM="${FILE_MEM}" +FILE_SIG="${FILE_SIG}"

################################################################################
# targets
################################################################################

all: sim

lint: ${HDL}
	${VERILATOR} --lint-only ${HDL} --top ${TOP}

compile: ${HDL}
	${VERILATOR} ${VFLAGS} ${MCR} ${PAR} --top ${TOP} ${HDL}

sim: compile
	obj_dir/V${TOP} ${ARG}
#	${VERILATOR_COVERAGE} --annotate logs/annotated logs/coverage.dat
