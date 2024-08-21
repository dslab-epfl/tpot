#pragma once

#include "net/packet.h"

enum net_transmit_flags {
	NONE = 0,
	UPDATE_ETHER_ADDRS = 1 << 0,
};

// Transmit the given packet on the given device, with the given flags
void net_transmit(struct net_packet* packet, device_t device, enum net_transmit_flags flags);

// Transmit the given packet unmodified to all devices except the packet's own
// TODO: This should not be necessary, it's only required because we can't properly deal with loops over devices during verification
void net_flood(struct net_packet* packet, enum net_transmit_flags flags);

// Transmit the given packet unmodified to devices except the packet's own and those marked as disabled
// TODO: Same note as above re: loops
void net_flood_except(struct net_packet* packet, bool* disabled_devices, enum net_transmit_flags flags);
