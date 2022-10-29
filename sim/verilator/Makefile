################################################################################
# HDL source files
################################################################################

VERILATOR?=verilator
VERILATOR_COVERAGE?=verilator_coverage

################################################################################
# HDL source files
################################################################################

# HDL path
PATH_HDL=../../hdl

# SystemVerilog RTL
RTL+=${PATH_HDL}/rtl/tcb_if.sv
RTL+=${PATH_HDL}/rtl/tcb_pas.sv
RTL+=${PATH_HDL}/rtl/tcb_arb.sv
RTL+=${PATH_HDL}/rtl/tcb_dec.sv
RTL+=${PATH_HDL}/rtl/tcb_reg.sv
RTL+=${PATH_HDL}/rtl/tcb_err.sv
# GPIO RTL
RTL+=${PATH_HDL}/rtl/gpio/tcb_gpio.sv
# UART RTL
RTL+=${PATH_HDL}/rtl/uart/tcb_uart_ser.sv
RTL+=${PATH_HDL}/rtl/uart/tcb_uart_des.sv
RTL+=${PATH_HDL}/rtl/uart/tcb_uart_fifo.sv
RTL+=${PATH_HDL}/rtl/uart/tcb_uart.sv

# SystemVerilog testbench
TSV+=${PATH_HDL}/tbn/tcb_pkg.sv
TSV+=${PATH_HDL}/tbn/tcb_mon.sv
TSV+=${PATH_HDL}/tbn/tcb_sub.sv
TSV+=${PATH_HDL}/tbn/tcb_man.sv
TSV+=${PATH_HDL}/tbn/tcb_tb.sv
## GPIO testbench
TSV+=${PATH_HDL}/tbn/gpio/tcb_gpio_tb.sv
## UART testbench
TSV+=${PATH_HDL}/tbn/uart/uart_model.sv
TSV+=${PATH_HDL}/tbn/uart/uart_model_tb.sv
TSV+=${PATH_HDL}/tbn/uart/tcb_uart_tb.sv

# combined HDL sources
HDL =${RTL}
HDL+=${TSV}

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

# set XLEN parameter
#XLEN ?= 32
#PAR += -GXLEN=${XLEN}

################################################################################
# Verilog $plusargs runtime arguments
################################################################################

#ARG += +FILE_MEM="${FILE_MEM}" +FILE_SIG="${FILE_SIG}"

################################################################################
#
################################################################################

all: sim

lint: ${HDL}
	${VERILATOR} --lint-only ${HDL} --top ${TOP}

compile: ${HDL}
	${VERILATOR} ${VFLAGS} ${MCR} ${PAR} --top ${TOP} ${HDL}

sim: compile
	obj_dir/V${TOP} ${ARG}
#	${VERILATOR_COVERAGE} --annotate logs/annotated logs/coverage.dat
