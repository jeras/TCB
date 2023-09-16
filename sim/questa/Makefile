include ../filelist.mk

TOP ?= tcb_lib_converter_tb

FLAGS = -suppress 13178

################################################################################
# Verilog toplevel parameter override
################################################################################

# TCB address/data bus widths
ABW ?= 32
DBW ?= 32
# TCB response delay
DLY ?= 2

#PAR += -GABW=${ABW}
#PAR += -GDBW=${DBW}
PAR += -GDLY=${DLY}

################################################################################
# Verilog $plusargs runtime arguments
################################################################################

#ARG += +FILE_MEM="${FILE_MEM}" +FILE_SIG="${FILE_SIG}"

################################################################################
# targets
################################################################################


all:
	qrun -makelib work -sv ${HDL} ${PAR} -end ${FLAGS} -top ${TOP}

gui:
	qrun -makelib work -sv ${HDL} ${PAR} -end ${FLAGS} -top ${TOP} -gui