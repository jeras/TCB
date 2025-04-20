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

# uncomment the GUI target for debugging purposes
#all: gui
all: run

run: ${HDL}
	qrun -makelib work -sv ${HDL} -end ${DEF} ${PAR} ${FLAGS} ${ARG} -top ${TOP}

gui:
	qrun -makelib work -sv ${HDL} -end ${DEF} ${PAR} ${FLAGS} ${ARG} -top ${TOP} -gui
