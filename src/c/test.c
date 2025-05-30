#include "test.h"

/**
 * Tests the GCD function.
 */
void test_gcd(void)
{
    struct
    {
        number_t a;
        number_t b;
        number_t expected;
    } tests[] = {
        {0, 0, 0},
        {1, 0, 1},
        {0, 1, 1},
        {1, 1, 1},
        {42, 56, 14},
        {56, 42, 14},
        {100, 25, 25},
        {25, 100, 25},
        {270, 192, 6},
        {1024, 256, 256},
        {9999, 9, 9},
        {360, 225, 45},
        {357, 234, 3},
        {123, 246, 123},
        {1000000, 500000, 500000},
        {99999998, 2, 2},
        {81, 153, 9},
        {9999, 1, 1},
        {123456789, 987654321, 9},
        {999999999999999998, 2, 2}};

    // Number of test cases
    size_t num_tests = sizeof(tests) / sizeof(tests[0]);

    // Run each test
    for (size_t i = 0; i < num_tests; i++)
    {
        number_t result = gcd(tests[i].a, tests[i].b);
        assert(result == tests[i].expected);
    }
}

/**
 * Tests the LCM function.
 */
void test_lcm(void)
{
    assert(lcm(4, 6) == 12);
    assert(lcm(12, 15) == 60);
}

/**
 * Tests the rational number functionality.
 */
void test_rational(void)
{
    rational_t r1 = rational_create(12, 6);
    assert(r1.numerator == 2);
    assert(r1.denominator == 1);

    rational_t r2 = rational_create(3, 7);

    rational_t r1_plus_r2 = rational_add(r1, r2);
    assert(r1_plus_r2.numerator == 17);
    assert(r1_plus_r2.denominator == 7);

    number_t rf = rational_floor(r2);
    assert(rf == 0);

    number_t rc = rational_ceil(r2);
    assert(rc == 1);

    rational_t r3 = rational_subtract(r1, r2);
    assert(r3.numerator == 11);
    assert(r3.denominator == 7);
}

/**
 * Tests the shorten function.
 */
void test_shorten(void)
{
    number_t a = 12;
    number_t b = 8;
    shorten(&a, &b);
    assert(a == 3);
    assert(b == 2);
}

/**
 * Tests the random number generation functions.
 */
void test_random(void)
{
    for (int i = 0; i < 100; i++)
    {
        const number_t a = random_number_including(1, 10);
        assert(a >= 1 && a <= 10);

        const rational_t b = rational_random_gt_0_lt_1();
        const double value_b = (double)b.numerator / (double)b.denominator;
        assert(value_b > 0 && value_b < 1);

        const rational_t c = rational_random_gt_1();
        const double value_c = (double)c.numerator / (double)c.denominator;
        assert(value_c > 1);

        const rational_t d = rational_random_ge_2();
        const double value_d = (double)d.numerator / (double)d.denominator;
        assert(value_d >= 2);

        const number_t e = number_random_gt_0();
        assert(e > 0 && e <= MAX_RANDOM);
    }
}

/**
 * Tests the lambda function by one example.
 * @param dx The pointer to the array that will hold the dx values.
 */
void test_lambda(number_t *dx)
{
    assert(lambda(2, 1, 1, 1, 0, 50, false, dx) == 4);
}

/**
 * Tests the find_period_length function.
 */
void test_find_period_length(void)
{
    //                 0  1  2  3  4  5  6  7  8  9
    number_t dx01[] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    assert(find_period_length(0, 9, dx01) == NO_PERIOD);

    //                 0  1  2  3  4  5  6  7  8  9
    number_t dx02[] = {1, 1, 1, 1, 1, 1, 1, 1, 1, 2};
    assert(find_period_length(0, 7, dx02) == 1);
    assert(find_period_length(0, 8, dx02) == 1);
    assert(find_period_length(0, 9, dx02) == NO_PERIOD);

    //                 0  1  2  3  4  5
    number_t dx03[] = {1, 2, 3, 1, 2, 3};
    assert(find_period_length(0, 5, dx03) == 3);

    //                 0  1  2  3  4  5  6
    number_t dx04[] = {1, 2, 3, 1, 2, 3, 1};
    assert(find_period_length(0, 6, dx04) == 3);

    //                 0  1  2  3  4  5  6
    number_t dx05[] = {1, 2, 3, 1, 2, 3, 4};
    assert(find_period_length(0, 6, dx05) == NO_PERIOD);

    number_t dx06[] = {1};
    assert(find_period_length(0, 0, dx06) == NO_PERIOD);

    //                 0  1  2  3
    number_t dx07[] = {5, 6, 5, 6};
    assert(find_period_length(0, 3, dx07) == 2);

    //                 0  1  2  3  4
    number_t dx08[] = {5, 6, 5, 6, 5};
    assert(find_period_length(0, 4, dx08) == 2);

    //                 0  1  2  3  4
    number_t dx09[] = {5, 6, 5, 6, 6};
    assert(find_period_length(0, 4, dx09) == NO_PERIOD);

    //                 0  1  2  3  4
    number_t dx10[] = {5, 6, 5, 6, 1};
    assert(find_period_length(0, 4, dx10) == NO_PERIOD);
    assert(find_period_length(0, 3, dx10) == 2);

    number_t dx11[] = {1, 1};
    assert(find_period_length(0, 1, dx11) == 1);

    //                 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
    number_t dx12[] = {3, 3, 1, 2, 2, 3, 3, 1, 2, 2, 3, 3, 1, 2, 2, 3};
    assert(find_period_length(0, 15, dx12) == 5);

    //                 0  1  2  3  4  5  6  7  8
    number_t dx13[] = {1, 2, 3, 1, 2, 3, 1, 2, 3};
    assert(find_period_length(0, 8, dx13) == 3);

    //                 0  1  2  3  4  5  6  7  8  9 10 11
    number_t dx14[] = {1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3};
    assert(find_period_length(0, 11, dx14) == 3);

    //                 0  1  2  3  4  5  6  7  8  9 10
    number_t dx15[] = {1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2};
    assert(find_period_length(0, 10, dx15) == 3);

    //                 0  1  2  3  4  5  6  7  8  9
    number_t dx16[] = {1, 2, 3, 1, 2, 3, 1, 2, 3, 1};
    assert(find_period_length(0, 9, dx16) == 3);

    //                 0  1  2  3  4  5  6  7  8  9 10 11 12 13
    number_t dx17[] = {2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3};
    assert(find_period_length(0, 13, dx17) == 3);
    assert(find_period_length(0, 12, dx17) == 3);
    assert(find_period_length(0, 11, dx17) == 3);
    assert(find_period_length(0, 10, dx17) == 3);
    assert(find_period_length(0, 9, dx17) == 3);
    assert(find_period_length(0, 8, dx17) == 3);
    assert(find_period_length(5, 13, dx17) == 3);

    //                 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14
    number_t dx18[] = {2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1};
    assert(find_period_length(0, 14, dx18) == 3);

    //                 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
    number_t dx19[] = {2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2};
    assert(find_period_length(0, 15, dx19) == 3);

    //                 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16
    number_t dx20[] = {2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 1};
    assert(find_period_length(0, 15, dx20) == 3);
    assert(find_period_length(0, 16, dx20) == NO_PERIOD);

    //                 0  1  2  3  4  5  6  7  8  9  10 11 12
    number_t dx21[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3};
    assert(find_period_length(0, 12, dx21) == NO_PERIOD);

    //                 0  1  2  3  4  5  6  7  8  9  10 11 12
    number_t dx22[] = {1, 2, 3, 1, 2, 3, 1, 2, 3, 10, 1, 2, 3};
    assert(find_period_length(0, 12, dx22) == NO_PERIOD);

    //                 0  1  2  3  4  5  6  7  8
    number_t dx23[] = {1, 2, 3, 4, 5, 1, 2, 3, 4};
    assert(find_period_length(0, 8, dx23) == NO_PERIOD);

    //                 0  1  2  3  4  5  6  7  8  9
    number_t dx24[] = {1, 2, 3, 4, 5, 6, 1, 2, 3, 4};
    assert(find_period_length(0, 9, dx24) == NO_PERIOD);

    //                 0  1  2  3  4  5  6  7  8  9 10
    number_t dx25[] = {1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4};
    assert(find_period_length(0, 10, dx25) == NO_PERIOD);

    //                 0  1  2  3  4  5  6  7  8  9 10 11
    number_t dx26[] = {1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4};
    assert(find_period_length(0, 11, dx26) == NO_PERIOD);
}

/**
 * Tests the sorting of the dx values.
 * It checks if the lambda function returns the same value
 * for sorted and unsorted dx values.
 * @param dx The pointer to the array that will hold the dx values.
 */
void test_sort(number_t *dx) {
    rational_t omega;
    number_t gamma, delta;

    for (int i = 0; i < 1000; i++)
    {
        printf("Sort test %d\n", i);

        do
            {
                gamma = number_random_gt_0();
                delta = number_random_gt_0();
            } while (delta == 0);
        omega = rational_create(gamma, delta);
        
        number_t alpha = number_random_gt_0();
        number_t beta = number_random_gt_0();
        shorten(&alpha, &beta);

        long lambda_sorted = lambda(alpha, beta, omega.numerator, omega.denominator, X_MIN, X_MAX, true, dx);
        long lambda_unsorted = lambda(alpha, beta, omega.numerator, omega.denominator, X_MIN, X_MAX, false, dx);
        assert(lambda_sorted == lambda_unsorted);
    }
}

/**
 * Tests the lambda function with a test file.
 * @param filename The name of the test file.
 * @param x_max The maximum value of x.
 * @param sort Indicates whether to sort the dx values.
 * @param dx The pointer to the array that will hold the dx values.
 */
int test_with_test_file(const char *filename, number_t x_max, bool sort, number_t *dx)
{
    clock_t start = clock();

    FILE *file = fopen(filename, "r");
    if (!file)
    {
        fprintf(stderr, "Tried to read: %s\n", filename);
        perror("Failed to open file");
        return EXIT_FAILURE;
    }

    char line[256];

    // Read and skip the header
    if (fgets(line, sizeof(line), file) == NULL)
    {
        perror("Error reading header");
        fclose(file);
        return EXIT_FAILURE;
    }

    int o_n, o_d, a_n, a_d;
    long expected_period_length;
    int counter = 0;

    // Read each line and extract integers
    while (fgets(line, sizeof(line), file))
    {
        if (sscanf(line, "%d,%d,%d,%d,%ld", &o_n, &o_d, &a_n, &a_d, &expected_period_length) == 5)
        {
            long computed_lambda = lambda(a_n, a_d, o_n, o_d, -10, x_max, sort, dx);
            printf("Read: %d -- %d, %d, %d, %d, %ld = %ld (computed)?\n", ++counter, o_n, o_d, a_n, a_d, expected_period_length, computed_lambda);
            assert(expected_period_length == computed_lambda);
        }
        else
        {
            fprintf(stderr, "Malformed line: %s\n", line);
        }
    }

    fclose(file);
    clock_t end = clock();
    double elapsed_time = (double)(end - start) / CLOCKS_PER_SEC;
    printf("Execution time: %f seconds\n", elapsed_time);

    return EXIT_SUCCESS;
}

/**
 * Creates test data for the lambda function.
 * Writes the data to a file in CSV format.
 * The first line contains the header.
 * The subsequent lines contain the values of o_n, o_d, a_n, a_d, and period.
 *
 * @param filename The name of the file to write the data to.
 * @param number_of_tests The number of tests to generate.
 * @param dx The pointer to the array that will hold the dx values.
 */
void create_test_data(const char *filename, const int number_of_tests, number_t *dx)
{
    FILE *file = fopen(filename, "w");
    if (!file)
    {
        fprintf(stderr, "Error: Failed to open file %s for writing.\n", filename);
        return;
    }

    // Write the header
    fprintf(file, "o_n,o_d,a_n,a_d,period\n");

    for (int i = 0; i < number_of_tests; i++)
    {
        const rational_t o = rational_random_gt_1();
        const rational_t a = rational_random_gt_1();
        const long period_length = lambda(a.numerator, a.denominator, o.numerator, o.denominator, 0, 1000000, false, dx);

        if (is_legal_period_length(period_length))
        {
            fprintf(file, "%lld,%lld,%lld,%lld,%ld\n", o.numerator, o.denominator, a.numerator, a.denominator, period_length);
        }
    }

    fclose(file);
    printf("Data to find patterns written to %s\n", filename);
}

/**
 * Tests the speed of the lambda function.
 * The test is performed by measuring the execution time of the function.
 *
 * @param dx The pointer to the array that will hold the dx values.
 */
void test_speed(number_t *dx)
{
    // about 1100 times faster than the Rust implementation!
    clock_t start = clock();
    long l = lambda(37033, 4687, 51, 4, 0, 1000000, false, dx);
    assert(l == 531930);
    double elapsed_time = (double)(clock() - start) / CLOCKS_PER_SEC;
    printf("Execution time: %f seconds\n", elapsed_time);
}

/**
 * Wrapper function for all tests.
 * It calls all the individual test functions.
 *
 * @param created_file_to_find_a_pattern Indicates whether to create a
 *        file to find a pattern.
 * @param dx The pointer to the array that will hold the dx values.
 */
void test(bool create_file_to_find_a_pattern, number_t *dx)
{
    test_gcd();
    test_lcm();
    test_rational();
    test_shorten();
    test_random();
    test_find_period_length();
    test_lambda(dx);
    test_speed(dx);
    test_sort(dx);
    test_with_test_file(TEST_FILE, X_MAX, false, dx);

    if (create_file_to_find_a_pattern)
    {
        char output_filename[256];
        const int number_of_tests = NUMBER_OF_LINES_IN_THE_PATTERN_FILE;
        snprintf(output_filename, sizeof(output_filename), FILE_TO_FIND_PATTERN, number_of_tests);
        create_test_data(output_filename, number_of_tests, dx);
    }
}
