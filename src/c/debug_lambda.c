#include <stdio.h>
#include <stdlib.h>
#include "mathematics.h"

int main(void)
{
    // Allocate just enough for small tests
    size_t sz = 10000000;
    number_t *dx = malloc(sz * sizeof(number_t));
    if (!dx) { perror("malloc"); return 1; }

    for (int xm = 50; xm <= 2000; xm += 50) {
        long s = lambda(2, 1, 69986, 35837, 0, xm, true, dx);
        long u = lambda(2, 1, 69986, 35837, 0, xm, false, dx);
        printf("x_max=%d: sorted=%ld unsorted=%ld\n", xm, s, u);
    }

    free(dx);
    return 0;
}
