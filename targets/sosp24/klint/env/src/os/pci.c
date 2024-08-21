#include "os/pci.h"

#include "os/memory.h"

static struct os_pci_address addresses[] = {OS_CONFIG_DATA};

size_t os_pci_enumerate(struct os_pci_address** out_addresses)
{
	size_t count = sizeof(addresses) / sizeof(struct os_pci_address);
	*out_addresses = os_memory_alloc(count, sizeof(struct os_pci_address));
	os_memory_copy(addresses, *out_addresses, sizeof(addresses));
	return count;
}
