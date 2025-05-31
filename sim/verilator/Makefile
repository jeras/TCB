################################################################################
# documentation
################################################################################

# https://veripool.org/guide/latest/exe_verilator.html

################################################################################
# DUT, TOP and source files
################################################################################

# source files
include ../filelist.mk

include ../tcb_pkg.mk
include ../tcb_bus_parameters.mk

# top level module
TOP ?= tcb_vip_tb

################################################################################
# tool specific flags
################################################################################

# specify SystemVerilog LRM version
#VFLAGS += +1800-2012ext+sv
# Generate binary executable
VFLAGS += --binary
# Optimize
VFLAGS += -O3
# Number of CPU threads
VFLAGS += -j 0
# optimize for speed or maximize finding X assign issues
VFLAGS += --x-assign fast
#VFLAGS += --x-assign 0
#VFLAGS += --x-assign 1
#VFLAGS += --x-assign unique
# Warn about lint issues; may not want this on less solid designs
#VFLAGS += -Wall
# Check SystemVerilog assertions
VFLAGS += --assert
# Generate coverage analysis
#VFLAGS += --coverage

# Run Verilator in debug mode
#VFLAGS += --debug
# Add this trace to get a backtrace in gdb
#VFLAGS += --gdbbt

# Make waveforms
#ifdef TRACE_DEBUG
VFLAGS += --trace-fst
VFLAGS += --trace-structs
#endif

################################################################################
# Verilog define macros
################################################################################

# example
# DEF += -Dmacro
# DEF += -Dmacro=value

# define TOOL_* macro (used to handle tool quirks)
DEF = -DTOOL_VERILATOR

# define macro VERILATOR is already predefined in Verilator

################################################################################
# Verilog toplevel parameter override
################################################################################

# example
# PAR += -Gparameter=value

# list of parameter overrides

# protocol
BUS_PAR += -GBUS_DLY=${HSK.DLY}
# signal widths
BUS_PAR += -GBUS_UNT=${BUS_UNT}
BUS_PAR += -GBUS_ADR=${BUS_ADR}
BUS_PAR += -GBUS_DAT=${BUS_DAT}
# PMA parameters
BUS_PAR += -GBUS_ALN=${BUS_ALN}
BUS_PAR += -GBUS_MIN=${BUS_MIN}
BUS_PAR ?= -GBUS_MOD=${BUS_MOD}
BUS_PAR ?= -GBUS_ORD=${BUS_ORD}
# channel configuration
BUS_PAR ?= -GCHN_CHN=${BUS_CHN}

# combined manager/subordinate parameters
PAR = ${BUS_PAR}

################################################################################
# Verilog plusargs
################################################################################

# example
# ARG += +key
# ARG += +key=value

################################################################################
# targets
################################################################################

all: simulate

lint: ${HDL}
	verilator --lint-only ${DEF} ${PAR} --top ${TOP} ${HDL}

compile: ${HDL}
	verilator ${VFLAGS} ${DEF} ${PAR} --top ${TOP} ${HDL}

simulate: compile
	obj_dir/V${TOP} ${ARG}
#	verilator_coverage --annotate logs/annotated logs/coverage.dat
