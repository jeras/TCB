################################################################################
# TCB physical interface parameter structure
################################################################################

# protocol
MAN_DLY ?= 0
# signal widths
MAN_UNT ?= 8
MAN_ADR ?= 17
MAN_DAT ?= 32
MAN_ALN ?= 0
# data packing parameters
MAN_SIZ ?= ${TCB_LOGARITHMIC}
MAN_MOD ?= ${TCB_BYTE_ENA}
MAN_ORD ?= ${TCB_DESCENDING}
# channel configuration
MAN_CHN ?= ${TCB_COMMON_HALF_DUPLEX}

# protocol
SUB_DLY ?= 0
# signal widths
SUB_UNT ?= 8
SUB_ADR ?= 17
SUB_DAT ?= 32
SUB_ALN ?= 0
# data packing parameters
SUB_SIZ ?= ${TCB_LOGARITHMIC}
SUB_MOD ?= ${TCB_BYTE_ENA}
SUB_ORD ?= ${TCB_DESCENDING}
# channel configuration
SUB_CHN ?= ${TCB_COMMON_HALF_DUPLEX}
