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
        TEST = 1 << 0,             // 0b00000001
        TEST_CONJECTURES = 1 << 1, // 0b00000010
    };

    TASKS;

    if (tasks & TEST) {
        const bool create_file_to_find_a_pattern = CREATE_FILE_TO_FIND_A_PATTERN;
        test(create_file_to_find_a_pattern, dx);
    }
    if (tasks & TEST_CONJECTURES)
        test_conjectures(dx);

    free(dx);
    return 0;
}
