################################################################################
# DUT, TOP and source files
################################################################################

# source files
include ../filelist.mk

# top level module
TOP ?= tcb_vip_tb
TESTBENCH ?= ../../hdl/tbn/lib/tcb_lib_logsize2byteena_tb.sv

# remove tetbench TOP from HDL list of files
DESIGN = $(filter-out ${TESTBENCH},${HDL})

################################################################################
# targets
################################################################################

concat:
	echo ${DESIGN}
	echo ${TESTBENCH}
	cat ${DESIGN} > design.sv
	cat ${TESTBENCH} > testbench.sv
