################################################################################
# documentation
################################################################################

# https://docs.amd.com/r/en-US/ug900-vivado-logic-simulation/Vivado-Simulator-Quick-Reference-generic_topuide
# https://docs.amd.com/r/en-US/ug900-vivado-logic-simulation/Elaborating-and-generic_topenerating-a-Design-Snapshot-xelab
# https://docs.amd.com/r/en-US/ug900-vivado-logic-simulation/Simulating-the-Design-Snapshot-xsim

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

# TODO, should be used on elab
FLAGS = -debug all

################################################################################
# Verilog define macros
################################################################################

# example
# DEF += -d macro
# DEF += -d macro=value

# define TOOL_* macro (used to handle tool quirks)
DEF = -d TOOL_VIVADO_SIMULATOR

################################################################################
# Verilog toplevel parameter override
################################################################################

# example
# PAR += -generic_top generic/parameter=value

# list of parameter overrides

# protocol
BUS_PAR += -generic_top HSK.DLY=${HSK.DLY}
# signal widths
BUS_PAR += -generic_top BUS_UNT=${BUS_UNT}
BUS_PAR += -generic_top BUS_ADR=${BUS_ADR}
BUS_PAR += -generic_top BUS_DAT=${BUS_DAT}
# data packing parameters
BUS_PAR += -generic_top BUS_ALN=${BUS_ALN}
BUS_PAR += -generic_top BUS_MIN=${BUS_MIN}
BUS_PAR ?= -generic_top BUS_MOD=${BUS_MOD}
BUS_PAR ?= -generic_top BUS_ORD=${BUS_ORD}
# channel configuration
BUS_PAR ?= -generic_top CHN_CHN=${BUS_CHN}

# combined manager/subordinate parameters
#PAR = ${BUS_PAR}

################################################################################
# Verilog plusargs
################################################################################

# example
# ARG += -testplusarg key
# ARG += -testplusarg key=value


################################################################################
# targets
################################################################################

# uncomment the GUI target for debugging purposes
#all: gui
all: simulate

compile: ${HDL}
	xvlog ${DEF} -sv ${HDL}

elaborate: compile
	xelab ${FLAGS} ${PAR} work.${TOP} -s ${TOP}

simulate: elaborate
	xsim ${ARG} ${TOP} -R

gui: elaborate
	xsim ${ARG} ${TOP} -gui
