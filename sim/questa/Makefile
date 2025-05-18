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
BUS_PAR += -GBUS_DLY=${HSK.DLY}
# signal widths
BUS_PAR += -GBUS_UNT=${BUS_UNT}
BUS_PAR += -GBUS_ADR=${BUS_ADR}
BUS_PAR += -GBUS_DAT=${BUS_DAT}
# data packing parameters
BUS_PAR += -GBUS_ALN=${BUS_ALN}
BUS_PAR += -GBUS_MIN=${BUS_MIN}
BUS_PAR ?= -GBUS_MOD=${BUS_MOD}
BUS_PAR ?= -GBUS_ORD=${BUS_ORD}
# channel configuration
BUS_PAR ?= -GCHN_CHN=${BUS_CHN}

# combined manager/subordinate parameters
#PAR = ${BUS_PAR}

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
