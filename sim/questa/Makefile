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

# TODO: add comment regarding this flag.
# I think it is suppressing errors on clock transition at time 0.
FLAGS  = -suppress 13178
# suppress error caused by mixing combinational/sequential elements in the same unpacked array
FLAGS += -suppress 7033
# disable optimizations
FLAGS += -voptargs=+acc

################################################################################
# Verilog define macros
################################################################################

# example
# DEF += -defineall macro
# DEF += -defineall macro=value

# define TOOL_* macro (used to handle tool quirks)
DEF = -defineall TOOL_QUESTA

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
#PAR = ${PHY_PAR}

################################################################################
# Verilog plusargs
################################################################################

# example
# ARG += +key
# ARG += +key=value

################################################################################
# targets
################################################################################

# uncomment the GUI target for debugging purposes
#all: gui
all: run

run: ${HDL}
	qrun -makelib work -sv ${HDL} -end ${DEF} ${PAR} ${FLAGS} ${ARG} -top ${TOP}

gui:
	qrun -makelib work -sv ${HDL} -end ${DEF} ${PAR} ${FLAGS} ${ARG} -top ${TOP} -gui
