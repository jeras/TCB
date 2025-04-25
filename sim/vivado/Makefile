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
include ../tcb_phy_parameters.mk

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
PHY_PAR += -generic_top PHY_DLY=${PHY_DLY}
# signal widths
PHY_PAR += -generic_top PHY_UNT=${PHY_UNT}
PHY_PAR += -generic_top PHY_ADR=${PHY_ADR}
PHY_PAR += -generic_top PHY_DAT=${PHY_DAT}
# data packing parameters
PHY_PAR += -generic_top PHY_ALN=${PHY_ALN}
PHY_PAR += -generic_top PHY_MIN=${PHY_MIN}
PHY_PAR ?= -generic_top PHY_MOD=${PHY_MOD}
PHY_PAR ?= -generic_top PHY_ORD=${PHY_ORD}
# channel configuration
PHY_PAR ?= -generic_top CHN_CHN=${PHY_CHN}

# combined manager/subordinate parameters
#PAR = ${PHY_PAR}

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
	xvlog ${FLAGS} ${DEF} -sv ${HDL}

elaborate: compile
	xelab ${PAR} work.${TOP} -s ${TOP}

simulate: elaborate
	xsim ${ARG} ${TOP} -R

gui: elaborate
	xsim ${ARG} ${TOP} -gui
