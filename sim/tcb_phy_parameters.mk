################################################################################
# TCB physical interface parameter structure
################################################################################

# protocol
MAN_DLY ?= 0
# signal widths
MAN_SLW ?= 8
MAN_ABW ?= 17
MAN_DBW ?= 32
MAN_ALW ?= 0
# data packing parameters
MAN_SIZ ?= ${TCB_LOGARITHMIC}
MAN_MOD ?= ${TCB_MEMORY}
MAN_ORD ?= ${TCB_DESCENDING}
# channel configuration
MAN_CHN ?= ${TCB_COMMON_HALF_DUPLEX}

# protocol
SUB_DLY ?= 0
# signal widths
SUB_SLW ?= 8
SUB_ABW ?= 17
SUB_DBW ?= 32
SUB_ALW ?= 0
# data packing parameters
SUB_SIZ ?= ${TCB_LOGARITHMIC}
SUB_MOD ?= ${TCB_MEMORY}
SUB_ORD ?= ${TCB_DESCENDING}
# channel configuration
SUB_CHN ?= ${TCB_COMMON_HALF_DUPLEX}
