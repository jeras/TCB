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
