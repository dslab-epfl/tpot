.PHONY: default check clean

default: check

clean:
	rm -f generated.c

generated.c: memory.h early_alloc.c ../original/include/*.h
	cat macros.h > generated.c
	clang -I ../original -E -CC -P -Wno-comment -Wno-invalid-pp-token early_alloc.c >> generated.c

check: generated.c
	verifast -shared -allow_dead_code -link_should_fail generated.c

