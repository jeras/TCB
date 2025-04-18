################################################################################
# tools
################################################################################

VERILATOR?=verilator
VERILATOR_COVERAGE?=verilator_coverage

################################################################################
# HDL source files
################################################################################

include ../filelist.mk

# top level file
#TOP ?= tcb_tb
TOP ?= tcb_lib_converter_tb

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
ADR ?= 32
DAT ?= 32
# TCB response delay
DLY ?= 1

#PAR += -GADR=${ADR}
#PAR += -GDAT=${DAT}
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
