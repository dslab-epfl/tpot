#pragma once

// We offload the endianness detection to the compiler here

#define swap16(val) ((val << 8) | (val >> 8))
#define swap32(val) ((val << 24) | ((val << 8) & 0xFF) | ((val >> 8) & 0xFF) | (val >> 24))
#define swap64(val) ((val << 56) | ((val << 40) & 0xFF) | ((val << 24) & 0xFF) | ((val << 8) & 0xFF) | ((val >> 8) & 0xFF) | ((val >> 24) & 0xFF) | ((val >> 40) & 0xFF) | (val >> 56))

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define cpu_to_le16(x) (x)
#define cpu_to_le32(x) (x)
#define cpu_to_le64(x) (x)
#define cpu_to_be16(x) swap16(x)
#define cpu_to_be32(x) swap32(x)
#define cpu_to_be64(x) swap64(x)
#define le_to_cpu16(x) (x)
#define le_to_cpu32(x) (x)
#define le_to_cpu64(x) (x)
#define be_to_cpu16(x) swap16(x)
#define be_to_cpu32(x) swap32(x)
#define be_to_cpu64(x) swap64(x)
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#define cpu_to_le16(x) swap16(x)
#define cpu_to_le32(x) swap32(x)
#define cpu_to_le64(x) swap64(x)
#define cpu_to_be16(x) (x)
#define cpu_to_be32(x) (x)
#define cpu_to_be64(x) (x)
#define le_to_cpu16(x) swap16(x)
#define le_to_cpu32(x) swap32(x)
#define le_to_cpu64(x) swap64(x)
#define be_to_cpu16(x) (x)
#define be_to_cpu32(x) (x)
#define be_to_cpu64(x) (x)
#else
#error Unknown endianness
#endif
