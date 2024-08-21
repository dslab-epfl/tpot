#include <stddef.h>

extern int main(int argc, char** argv);

void _start(void) { main(0, NULL); }
