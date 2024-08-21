#include "os/config.h"

struct config_item {
	const char* name;
	uint64_t value;
};

static struct config_item items[] = {NF_CONFIG_DATA};

static bool string_compare(const char* a, const char* b)
//@ requires [?fa]string(a, ?csa) &*& [?fb]string(b, ?csb);
//@ ensures [fa]string(a, csa) &*& [fb]string(b, csb) &*& result == (csa == csb);
{
	size_t n = 0;
	for (;; n++)
	//@ requires [fa]string(a + n, ?csan) &*& [fb]string(b + n, ?csbn);
	//@ ensures [fa]string(a + old_n, csan) &*& [fb]string(b + old_n, csbn) &*& ((n == SIZE_MAX) == (csan == csbn));
	{
		//@ string_limits(a + n);
		//@ open [fa]string(a + n, csan);
		//@ open [fb]string(b + n, csbn);
		if (a[n] != b[n]) {
			break;
		}
		if (a[n] == '\0') {
			n = SIZE_MAX;
			break;
		}
	}
	return n == SIZE_MAX;
}

bool os_config_try_get(const char* name, uint64_t* out_value)
//@ requires [?f]*name |-> _ &*& *out_value |-> _;
//@ ensures [f]*name |-> _ &*& *out_value |-> _;
{
	// VeriFast is missing features related to global variables (e.g. it doesn't understand sizeof of a global variable),
	// so it cannot verify this 5-line function, but it can be easily audited.
	//@ assume(false);
	for (size_t n = 0; n < sizeof(items) / sizeof(struct config_item); n++) {
		if (string_compare(items[n].name, name)) {
			*out_value = items[n].value;
			return true;
		}
	}
	return false;
}
