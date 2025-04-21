################################################################################
# documentation
################################################################################

# https://docs.amd.com/r/en-US/ug900-vivado-logic-simulation/Vivado-Simulator-Quick-Reference-generic_topuide
# https://docs.amd.com/r/en-US/ug900-vivado-logic-simulation/Elaborating-and-generic_topenerating-a-Design-Snapshot-xelab
# https://docs.amd.com/r/en-US/ug900-vivado-logic-simulation/Simulating-the-Design-Snapshot-xsim

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
MAN_PAR += -generic_top MAN_DLY=${MAN_DLY}
# signal widths
MAN_PAR += -generic_top MAN_UNT=${MAN_UNT}
MAN_PAR += -generic_top MAN_ADR=${MAN_ADR}
MAN_PAR += -generic_top MAN_DAT=${MAN_DAT}
# data packing parameters
MAN_PAR += -generic_top MAN_ALN=${MAN_ALN}
MAN_PAR += -generic_top MAN_MIN=${MAN_MIN}
MAN_PAR ?= -generic_top MAN_MOD=${MAN_MOD}
MAN_PAR ?= -generic_top MAN_ORD=${MAN_ORD}
# channel configuration
MAN_PAR ?= -generic_top CHN_CHN=${MAN_CHN}

# protocol
SUB_PAR += -generic_top SUB_DLY=${SUB_DLY}
# signal widths
SUB_PAR += -generic_top SUB_UNT=${SUB_UNT}
SUB_PAR += -generic_top SUB_ADR=${SUB_ADR}
SUB_PAR += -generic_top SUB_DAT=${SUB_DAT}
# data packing parameters
SUB_PAR += -generic_top SUB_ALN=${SUB_ALN}
SUB_PAR += -generic_top SUB_MIN=${SUB_MIN}
SUB_PAR ?= -generic_top SUB_MOD=${SUB_MOD}
SUB_PAR ?= -generic_top SUB_ORD=${SUB_ORD}
# channel configuration
SUB_PAR ?= -generic_top CHN_CHN=${SUB_CHN}

# combined manager/subordinate parameters
PAR = ${MAN_PAR} ${SUB_PAR}

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
