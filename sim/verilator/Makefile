################################################################################
# documentation
################################################################################

# https://veripool.org/guide/latest/exe_verilator.html

################################################################################
# DUT, TOP and source files
################################################################################

include ../filelist.mk

include ../tcb_pkg.mk
include ../tcb_phy_parameters.mk

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
MAN_PAR += -GMAN_DLY=${MAN_DLY}
# signal widths
MAN_PAR += -GMAN_UNT=${MAN_UNT}
MAN_PAR += -GMAN_ADR=${MAN_ADR}
MAN_PAR += -GMAN_DAT=${MAN_DAT}
# data packing parameters
MAN_PAR += -GMAN_ALN=${MAN_ALN}
MAN_PAR += -GMAN_MIN=${MAN_MIN}
MAN_PAR ?= -GMAN_MOD=${MAN_MOD}
MAN_PAR ?= -GMAN_ORD=${MAN_ORD}
# channel configuration
MAN_PAR ?= -GCHN_CHN=${MAN_CHN}

# protocol
SUB_PAR += -GSUB_DLY=${SUB_DLY}
# signal widths
SUB_PAR += -GSUB_UNT=${SUB_UNT}
SUB_PAR += -GSUB_ADR=${SUB_ADR}
SUB_PAR += -GSUB_DAT=${SUB_DAT}
# data packing parameters
SUB_PAR += -GSUB_ALN=${SUB_ALN}
SUB_PAR += -GSUB_MIN=${SUB_MIN}
SUB_PAR ?= -GSUB_MOD=${SUB_MOD}
SUB_PAR ?= -GSUB_ORD=${SUB_ORD}
# channel configuration
SUB_PAR ?= -GCHN_CHN=${SUB_CHN}

# combined manager/subordinate parameters
PAR = ${MAN_PAR} ${SUB_PAR}

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
