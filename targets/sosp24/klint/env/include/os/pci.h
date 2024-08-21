#pragma once

#include "arch/io.h"

#include <stddef.h>
#include <stdint.h>

// Physical addresses at which we can talk to PCI via geographical addressing
#define PCI_CONFIG_ADDR 0xCF8
#define PCI_CONFIG_DATA 0xCFC

struct os_pci_address {
	uint8_t bus;
	uint8_t device;
	uint8_t function;
	uint8_t _padding[5];
};

// Returns the number of devices
size_t os_pci_enumerate(struct os_pci_address** out_addresses);

// Reads the given register of the device at the given address and return its value.
static inline uint32_t os_pci_read(const struct os_pci_address* address, const uint8_t reg)
{
	io_port_out32(PCI_CONFIG_ADDR, 0x80000000u | ((uint32_t) address->bus << 16) | ((uint32_t) address->device << 11) | ((uint32_t) address->function << 8) | reg);
	// Wait til the out32 is done
	io_port_out8(0x80, 0);
	return io_port_in32(PCI_CONFIG_DATA);
}

// Writes the given value to the given register of the device at the given address
static inline void os_pci_write(const struct os_pci_address* address, const uint8_t reg, const uint32_t value)
{
	io_port_out32(PCI_CONFIG_ADDR, 0x80000000u | ((uint32_t) address->bus << 16) | ((uint32_t) address->device << 11) | ((uint32_t) address->function << 8) | reg);
	// Wait til the out32 is done
	io_port_out8(0x80, 0);
	io_port_out32(PCI_CONFIG_DATA, value);
}
