# Root of the project
ROOT = $(dir $(firstword $(MAKEFILE_LIST)))

# Path to rustc executable
RUSTC ?= rustc

# Flags to pass rustc
RUSTC_FLAGS ?=

SRC = $(shell find $(ROOT)src -name '*.rs')

TARGET ?= target

LIBHDRGEN = $(TARGET)/libhdrgen.timestamp

all: $(LIBHDRGEN)

clean:
	rm -f $(TARGET)/libhdrgen*

clean-all: clean

$(LIBHDRGEN): $(SRC) | $(TARGET)
	$(RUSTC) $(RUSC_FLAGS) --out-dir $(TARGET) --crate-type=rlib $(ROOT)src/lib.rs
	touch $@

$(TARGET):
	mkdir -p $@

.PHONY: all clean clean-all

.SUFFIXES:
