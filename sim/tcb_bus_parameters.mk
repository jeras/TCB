################################################################################
# TCB physical interface parameter structure
################################################################################

# protocol
HSK_DLY ?= 0
# signal widths
BUS_UNT ?= 8
BUS_ADR ?= 32
BUS_DAT ?= 32
# data packing parameters
BUS_ALN ?= 0
BUS_MIN ?= 0
BUS_MOD ?= ${TCB_BYTE_ENA}
BUS_ORD ?= ${TCB_DESCENDING}
# channel configuration
BUS_CHN ?= ${TCB_HALF_DUPLEX}
