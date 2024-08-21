# Get current dir, see https://stackoverflow.com/a/8080530
OS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# Our sources
OS_SRCS += $(shell echo $(OS_DIR)/*.c)

# Force the use of our own time_t by preventing the stdlib from defining it and forcefully including ours so it's available (same workaround as linux/clock.c)
CFLAGS += -D__time_t_defined
CFLAGS += -D__DEFINED_time_t
CFLAGS += --include os/clock.h

# Bare-metal!
CFLAGS += -ffreestanding -nostdlib

ifneq (,$(findstring DEBUG_LEVEL,$(CFLAGS)))
$(error The baremetal OS does not support debug features.)
endif
