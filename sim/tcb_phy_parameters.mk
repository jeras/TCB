################################################################################
# TCB physical interface parameter structure
################################################################################

# protocol
PHY_DLY ?= 0
# signal widths
PHY_UNT ?= 8
PHY_ADR ?= 32
PHY_DAT ?= 32
# data packing parameters
PHY_ALN ?= 0
PHY_MIN ?= 0
PHY_MOD ?= ${TCB_BYTE_ENA}
PHY_ORD ?= ${TCB_DESCENDING}
# channel configuration
PHY_CHN ?= ${TCB_COMMON_HALF_DUPLEX}
