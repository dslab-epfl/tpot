#pragma once

#include "net/packet.h"
#include "net/tx.h" // transitive include as convenience for implementers
#include "os/config.h"

#include <stdbool.h>
#include <stdint.h>

// Network functions have two mandatory methods and can read from a config file
// The config file must be in the following format:
//   {"[key name]", [value: must be an integer]}
// Multiple entries like the above can be added but must be separated by a comma

// Initialize any necessary state required by the NF.
// This is where all the memory space required by the NF must be allocated
//  devices_count is the number of devices/interface available
//  returns whether the initialization succeeded
bool nf_init(device_t devices_count);
//@ requires devices_count > 0;
//@ ensures emp;

// Handles the given packet
// No memory allocation can be performed in this function
void nf_handle(struct net_packet* packet);
//@ requires *packet |-> _;
//@ ensures *packet |-> _;

// Convenience method to read a device from the config file, given the number of existing devices
static inline bool os_config_get_device(const char* name, device_t devices_count, device_t* out_value)
{
	uint64_t value;
	if (!os_config_get(name, 0, devices_count - 1, &value)) { // the max param is inclusive
		return false;
	}
	*out_value = (device_t) value;
	return true;
}
