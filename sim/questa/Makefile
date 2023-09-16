include ../filelist.mk

TOP ?= tcb_lib_converter_tb

FLAGS = -suppress 13178

all:
	qrun -makelib work -sv ${HDL} -end ${FLAGS} -top ${TOP}