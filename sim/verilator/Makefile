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
include ../tcb_phy_parameters.mk

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
PHY_PAR += -GPHY_DLY=${PHY_DLY}
# signal widths
PHY_PAR += -GPHY_UNT=${PHY_UNT}
PHY_PAR += -GPHY_ADR=${PHY_ADR}
PHY_PAR += -GPHY_DAT=${PHY_DAT}
# data packing parameters
PHY_PAR += -GPHY_ALN=${PHY_ALN}
PHY_PAR += -GPHY_MIN=${PHY_MIN}
PHY_PAR ?= -GPHY_MOD=${PHY_MOD}
PHY_PAR ?= -GPHY_ORD=${PHY_ORD}
# channel configuration
PHY_PAR ?= -GCHN_CHN=${PHY_CHN}

# combined manager/subordinate parameters
PAR = ${PHY_PAR}

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
