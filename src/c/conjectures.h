#ifndef CONJECTURES_H
#define CONJECTURES_H
#include "mathematics.h"

void test_conjectures(number_t *dx);
void test_conjecture_from_csv(const char *path);
void generate_conjecture_degenerate_csv(const char *path, int target_count, number_t *dx);

#endif /* CONJECTURES_H */
