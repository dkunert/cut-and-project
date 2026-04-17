#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "test.h"
#include "conjectures.h"

int main(int argc, const char *argv[])
{
    number_t *dx = dx_alloc(MAX_PERIOD_ARRAY_SIZE);

    enum Tasks
    {
        TEST = 1 << 0,                                   // 0b00000001
        TEST_CONJECTURES = 1 << 1,                       // 0b00000010
        TEST_CONJECTURE_7_FROM_CSV = 1 << 2,             // 0b00000100
        GENERATE_CONJECTURE_7_DEGENERATE_CSV = 1 << 3,   // 0b00001000
    };

    uint8_t tasks = TASKS;

    if (tasks & TEST) {
        const bool create_file_to_find_a_pattern = CREATE_FILE_TO_FIND_A_PATTERN;
        test(create_file_to_find_a_pattern, false, dx);
    }

    if (tasks & TEST_CONJECTURES)
        test_conjectures(dx);

    if (tasks & TEST_CONJECTURE_7_FROM_CSV)
        test_conjecture_7_from_csv(CONJECTURE_7_CSV_FILE);

    if (tasks & GENERATE_CONJECTURE_7_DEGENERATE_CSV)
        generate_conjecture_7_degenerate_csv(
            CONJECTURE_7_DEGENERATE_CSV_FILE,
            CONJECTURE_7_DEGENERATE_TARGET_COUNT,
            dx);

    free(dx);
    return 0;
}
