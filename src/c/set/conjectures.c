#include <stdio.h>
#include "conjectures.h"

typedef enum Conjecture
{
    CONJECTURE_0 = 1U << 0, // 0b0000 0001
} Conjecture;

/**
 * Tests the conjecture: lambda = N if D does not divide N, else N / D,
 * where N = floor(omega*alpha) + floor(omega*beta) + 1 and D = alpha^2 + beta^2
 *
 * @param dx The array of numbers.
 * @param conjecture The conjecture to test.
 * @param number_of_tests The number of tests to perform.
 */
void test_conjecture(number_t *dx, const Conjecture conjecture, const int number_of_tests)
{
    rational_t omega;
    number_t gamma, delta;

    for (size_t i = 0; i < number_of_tests; i++)
    {
        if (i % 100 == 0)
            printf("Test %zu of conjecture (lambda = N if D does not divide N, else N / D)\n", i + 1);

        do
        {
            gamma = number_random_gt_0();
            delta = number_random_gt_0();
        } while (delta == 0);
        omega = rational_create(gamma, delta);

        number_t alpha = number_random_gt_0();
        number_t beta = number_random_gt_0();
        shorten(&alpha, &beta);

        long computed_period_length = lambda(alpha, beta, omega.numerator, omega.denominator, X_MIN, X_MAX, true, dx);

        if (computed_period_length == NO_PERIOD)
        {
            printf("No period found for a = %lld/%lld and omega = %lld/%lld! Trying 10*X_MAX!\n", alpha, beta, omega.numerator, omega.denominator);
            computed_period_length = lambda(alpha, beta, omega.numerator, omega.denominator, X_MIN, 10 * X_MAX, false, dx);

            if (computed_period_length == NO_PERIOD)
            {
                printf("Still no period for X_MAX * 10!\n");
                continue;
            }
        }
        else if (computed_period_length == ARRAY_SIZE_EXCEEDED)
        {
            printf("Array size exceeded for a = %lld/%lld and omega = %lld/%lld!\n", alpha, beta, omega.numerator, omega.denominator);
            continue;
        }
        else if (computed_period_length == DX_LENGTH_TO_SMALL)
        {
            printf("Too many elements cut from dx for a = %lld/%lld and omega = %lld/%lld! Trying 10*X_MAX!\n", alpha, beta, omega.numerator, omega.denominator);
            computed_period_length = lambda(alpha, beta, omega.numerator, omega.denominator, X_MIN, 10 * X_MAX, false, dx);

            if (computed_period_length == DX_LENGTH_TO_SMALL)
            {
                printf("Still too many elements cut from dx for X_MAX * 10!\n");
                continue;
            }
        }
        else
        {
            // lambda = N if D does not divide N, else N / D,
            // where N = floor(omega*alpha) + floor(omega*beta) + 1 and D = alpha^2 + beta^2
            const number_t N = rational_floor((rational_t){omega.numerator * alpha, omega.denominator})
                             + rational_floor((rational_t){omega.numerator * beta, omega.denominator})
                             + 1;
            const number_t D = alpha * alpha + beta * beta;
            const number_t expected = (N % D == 0) ? N / D : N;
            if (computed_period_length != expected)
            {
                printf("Assertion for conjecture for a = %lld/%lld, omega = %lld/%lld, N = %lld, D = %lld, expected = %lld and lambda = %ld!\n", alpha, beta, omega.numerator, omega.denominator, N, D, expected, computed_period_length);
            }
        }
    }
}

/**
 * Tests the conjecture against observed period lengths stored in a CSV file.
 * The CSV must have the header "o_n,o_d,a_n,a_d,period" and one data row per line.
 * For each row, computes N = floor(o_n*alpha/o_d) + floor(o_n*beta/o_d) + 1
 * and D = alpha^2 + beta^2, then checks that the observed period equals
 * N if D does not divide N, else N / D.
 *
 * @param path The path to the CSV file.
 */
void test_conjecture_from_csv(const char *path)
{
    FILE *f = fopen(path, "r");
    if (f == NULL)
    {
        fprintf(stderr, "Error: could not open %s\n", path);
        exit(EXIT_FAILURE);
    }

    // Skip header line
    char buffer[256];
    if (fgets(buffer, sizeof(buffer), f) == NULL)
    {
        fprintf(stderr, "Error: empty file %s\n", path);
        fclose(f);
        exit(EXIT_FAILURE);
    }

    long long o_n, o_d, a_n, a_d, period;
    size_t total = 0, mismatches = 0;

    while (fscanf(f, "%lld,%lld,%lld,%lld,%lld", &o_n, &o_d, &a_n, &a_d, &period) == 5)
    {
        const number_t alpha = (number_t)a_n;
        const number_t beta = (number_t)a_d;
        const number_t N = rational_floor((rational_t){(number_t)o_n * alpha, (number_t)o_d})
                         + rational_floor((rational_t){(number_t)o_n * beta, (number_t)o_d})
                         + 1;
        const number_t D = alpha * alpha + beta * beta;
        const number_t expected = (N % D == 0) ? N / D : N;

        total++;
        if (expected != (number_t)period)
        {
            mismatches++;
            if (mismatches <= 10)
            {
                printf("Mismatch: omega = %lld/%lld, alpha = %lld, beta = %lld, N = %lld, D = %lld, expected = %lld, observed period = %lld\n",
                       o_n, o_d, (long long)alpha, (long long)beta,
                       (long long)N, (long long)D, (long long)expected, period);
            }
        }
    }

    fclose(f);

    printf("Conjecture test from CSV '%s': %zu rows checked, %zu mismatches.\n",
           path, total, mismatches);
}

/**
 * Generates a CSV of test cases that exercise the degenerate branch of
 * the conjecture (D | N, so lambda = N / D).
 * Scans small coprime (alpha, beta) and omega = p/q in lowest terms.
 * For each (alpha, beta, omega) with D | N, computes the actual period via
 * lambda() and writes a row "o_n,o_d,a_n,a_d,period".
 * Stops after target_count successful rows.
 *
 * @param path The output CSV path.
 * @param target_count The number of rows to generate.
 * @param dx The work array required by lambda().
 */
void generate_conjecture_degenerate_csv(const char *path, int target_count, number_t *dx)
{
    // Resume support: append if file exists and has content, else write fresh
    FILE *f_check = fopen(path, "r");
    bool resume = false;
    int existing_count = 0;
    if (f_check != NULL)
    {
        char buf[256];
        if (fgets(buf, sizeof(buf), f_check) != NULL)  // header
        {
            while (fgets(buf, sizeof(buf), f_check) != NULL)
                existing_count++;
        }
        fclose(f_check);
        if (existing_count > 0)
            resume = true;
    }

    FILE *f;
    if (resume)
    {
        f = fopen(path, "a");
        printf("Resuming: appending to '%s' (%d existing rows)\n", path, existing_count);
    }
    else
    {
        f = fopen(path, "w");
        fprintf(f, "o_n,o_d,a_n,a_d,period\n");
    }
    if (f == NULL)
    {
        fprintf(stderr, "Error: could not open %s for writing\n", path);
        exit(EXIT_FAILURE);
    }

    int count = existing_count;
    int generated = 0;
    size_t lambda_failures = 0;
    size_t formula_disagreements = 0;

    const number_t ALPHA_MAX = 10;
    const number_t BETA_MAX  = 10;
    const number_t Q_MAX     = 50;
    const number_t P_MAX     = 2000;

    // Skip counter for resume: skip the first existing_count matching candidates
    int skip = existing_count;

    for (number_t alpha = 1; alpha <= ALPHA_MAX && count < target_count; alpha++)
    {
        for (number_t beta = 1; beta <= BETA_MAX && count < target_count; beta++)
        {
            if (gcd(alpha, beta) != 1)
                continue;

            const number_t D = alpha * alpha + beta * beta;

            for (number_t q = 1; q <= Q_MAX && count < target_count; q++)
            {
                for (number_t p = 1; p <= P_MAX && count < target_count; p++)
                {
                    if (gcd(p, q) != 1)
                        continue;

                    const number_t N = (p * alpha) / q + (p * beta) / q + 1;
                    if (N < D || N % D != 0)
                        continue;

                    // Skip already-computed rows when resuming
                    if (skip > 0)
                    {
                        skip--;
                        continue;
                    }

                    // x_max must be >> omega so the 10% edge trim in lambda()
                    // covers the boundary corruption (which spans ~omega x-values).
                    const number_t omega_int = p / q + 1;
                    const number_t x_max_degenerate = MAX(1000, 25 * omega_int);
                    const number_t estimated_points = x_max_degenerate * N / D;
                    if (estimated_points > 10000000)
                    {
                        lambda_failures++;
                        continue;
                    }
                    printf("\rComputing: alpha=%lld, beta=%lld, omega=%lld/%lld, N=%lld, D=%lld, x_max=%lld ...          ",
                           (long long)alpha, (long long)beta, (long long)p, (long long)q,
                           (long long)N, (long long)D, (long long)x_max_degenerate);
                    fflush(stdout);
                    long lam = lambda(alpha, beta, p, q, X_MIN, x_max_degenerate, true, dx);
                    if (!is_legal_period_length(lam))
                    {
                        lambda_failures++;
                        printf("\rSkipped: alpha=%lld, beta=%lld, omega=%lld/%lld, N=%lld, D=%lld (lambda=%ld, failures=%zu)    ",
                               (long long)alpha, (long long)beta, (long long)p, (long long)q,
                               (long long)N, (long long)D, lam, lambda_failures);
                        fflush(stdout);
                        continue;
                    }

                    const number_t expected = N / D;
                    if (lam != expected)
                    {
                        formula_disagreements++;
                        fprintf(stderr, "Warning: lambda = %ld != N/D = %lld for alpha=%lld, beta=%lld, omega=%lld/%lld, N=%lld, D=%lld\n",
                                lam, (long long)expected, (long long)alpha, (long long)beta,
                                (long long)p, (long long)q, (long long)N, (long long)D);
                    }

                    fprintf(f, "%lld,%lld,%lld,%lld,%ld\n",
                            (long long)p, (long long)q, (long long)alpha, (long long)beta, lam);
                    fflush(f);
                    count++;
                    generated++;
                    printf("\r%d / %d", count, target_count);
                    fflush(stdout);
                }
            }
        }
    }

    fclose(f);
    printf("\nWrote %d new rows (%d total) to '%s' (lambda() failures skipped: %zu, formula disagreements: %zu).\n",
           generated, count, path, lambda_failures, formula_disagreements);
}

/**
 * Wrapper function for testing the conjecture.
 *
 * @param *dx The pointer to the array that will hold the dx values.
 */
void test_conjectures(number_t *dx)
{
    test_conjecture(dx, CONJECTURE_0, NUMBER_OF_NUMBER_OF_CONJECTURE_TESTS);
}
