include ../filelist.mk

include ../tcb_pkg.mk
include ../tcb_phy_parameters.mk

TOP ?= tcb_lib_converter_tb

################################################################################
# Verilog toplevel parameter override
################################################################################

# list of parameter overrides

# protocol
MAN_PAR += -GMAN_DLY=${MAN_DLY}
# signal widths
MAN_PAR += -GMAN_SLW=${MAN_SLW}
MAN_PAR += -GMAN_ABW=${MAN_ABW}
MAN_PAR += -GMAN_DBW=${MAN_DBW}
MAN_PAR += -GMAN_ALW=${MAN_ALW}
# data packing parameters
MAN_PAR ?= -GMAN_SIZ=${MAN_SIZ}
MAN_PAR ?= -GMAN_MOD=${MAN_MOD}
MAN_PAR ?= -GMAN_ORD=${MAN_ORD}
# channel configuration
MAN_PAR ?= -GCHN_CHN=${MAN_CHN}

# protocol
SUB_PAR += -GSUB_DLY=${SUB_DLY}
# signal widths
SUB_PAR += -GSUB_SLW=${SUB_SLW}
SUB_PAR += -GSUB_ABW=${SUB_ABW}
SUB_PAR += -GSUB_DBW=${SUB_DBW}
SUB_PAR += -GSUB_ALW=${SUB_ALW}
# data packing parameters
SUB_PAR ?= -GSUB_SIZ=${SUB_SIZ}
SUB_PAR ?= -GSUB_MOD=${SUB_MOD}
SUB_PAR ?= -GSUB_ORD=${SUB_ORD}
# channel configuration
SUB_PAR ?= -GCHN_CHN=${SUB_CHN}

# combined manager/subordinate parameters
PAR = ${MAN_PAR} ${SUB_PAR}

################################################################################
# Verilog $plusargs runtime arguments
################################################################################

#ARG += +FILE_MEM="${FILE_MEM}" +FILE_SIG="${FILE_SIG}"

################################################################################
# targets
################################################################################

FLAGS = -suppress 13178

all:
	qrun -makelib work -sv ${HDL} -end ${PAR} ${FLAGS} -top ${TOP}

gui:
	qrun -makelib work -sv ${HDL} -end ${PAR} ${FLAGS} -top ${TOP} -gui