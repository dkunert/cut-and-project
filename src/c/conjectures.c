#include <stdio.h>
#include <math.h>
#include <assert.h>
#include "conjectures.h"

typedef enum Conjecture
{
    CONJECTURE_2_1 = 1U << 0, // 0b0000 0001
    CONJECTURE_2_2 = 1U << 1, // 0b0000 0010
    CONJECTURE_3_0 = 1U << 2, // 0b0000 0100
    CONJECTURE_4_1 = 1U << 3, // 0b0000 1000
    CONJECTURE_4_2 = 1U << 4, // 0b0001 0000
    CONJECTURE_4_3 = 1U << 5, // 0b0010 0000
    CONJECTURE_5_0 = 1U << 6, // 0b0100 0000
    CONJECTURE_6_1 = 1U << 7, // 0b1000 0000
    CONJECTURE_6_2 = 1U << 8, // 0b0001 0000 0000
} Conjecture;

/**
 * Tests conjectures 2 to 6.
 * The conjectures are:
 * 2.1: lambda < alpha + beta + 1 for omega in (0, 1)
 * 2.2: lambda < alpha + beta + 1 for omega in (0, 1) and near 1
 * 3:   lambda = alpha + beta + 1 for omega = 1
 * 4.1: lambda >= alpha + beta + 1 for omega in (1, 2)
 * 4.2: lambda >= alpha + beta + 1 for omega in (1, 2) and near 1
 * 4.3: lambda >= alpha + beta + 1 for omega in (1, 2) and near 2
 * 5:   lambda > alpha + beta + 1 for omega >= 2
 * 6.1: lambda is about gamma/delta * (alpha + beta + 1)
 * 6.2: lambda is about gamma/delta * (alpha + beta + 1) with correction
 *
 * @param dx The array of numbers.
 * @param conjecture The conjecture to test.
 * @param number_of_tests The number of tests to perform.
 */
void test_concjeture2_to_6(number_t *dx, const Conjecture conjecture, const int number_of_tests)
{
    // CONJECTURE6_1 and CONJECTURE6_2 must be tested together

    bool print;

    rational_t omega;
    number_t gamma, delta;
    double prediction, error, mean_observed = 0.0, ss_res = 0.0, ss_tot_part, ss_tot = 0.0;

    for (size_t i = 0; i < number_of_tests; i++)
    {
        print = (i % 100 == 0);

        if (print)
            printf("Test %zu of conjecture", i + 1);

        switch (conjecture)
        {
        case CONJECTURE_2_1:
            if (print)
                printf("2.1 (lambda < alpha + beta + 1 for omega in (0, 1))\n");
            omega = rational_random_gt_0_lt_1();
            break;

        case CONJECTURE_2_2:
            if (print)
                printf("2.2 (lambda < alpha + beta + 1 for omega in (0, 1) and near 1)\n");
            gamma = number_random_gt_0();
            delta = gamma + 1;
            omega = rational_create(gamma, delta);
            break;

        case CONJECTURE_3_0:
            if (print)
                printf("3 (lambda = alpha + beta + 1 for omega = 1)\n");
            omega = rational_create(1, 1);
            break;

        case CONJECTURE_4_1:
            if (print)
                printf("4.1 (lambda >= alpha + beta + 1 for omega in (1, 2))\n");
            omega = rational_random_gt_1();
            break;

        case CONJECTURE_4_2:
            if (print)
                printf("4.2 (lambda >= alpha + beta + 1 for omega in (1, 2) and near 1)\n");
            do
            {
                gamma = number_random_gt_0();
                delta = gamma - 1;
            } while (delta == 0);
            omega = rational_create(gamma, delta);
            break;

        case CONJECTURE_4_3:
            if (print)
                printf("4.3 (lambda >= alpha + beta + 1 for omega in (1, 2) and near 2)\n");
            delta = number_random_gt_0();
            gamma = 2 * delta - 1;
            omega = rational_create(gamma, delta);
            break;

        case CONJECTURE_5_0:
            if (print)
                printf("5 (lambda > alpha + beta + 1 for omega >= 2)\n");
            omega = rational_random_ge_2();
            break;

        case CONJECTURE_6_1:
        case CONJECTURE_6_2:
            if (print)
                printf("6 (lambda = gamma/delta * (alpha + beta + 1) + correction * (gamma - delta))\n");
            do
            {
                gamma = number_random_gt_0();
                delta = number_random_gt_0();
            } while (delta == 0);
            omega = rational_create(gamma, delta);
            break;

        default:
            printf("Unknown conjecture: %d\n", conjecture);
            exit(EXIT_FAILURE);
        }

        number_t alpha = number_random_gt_0();
        number_t beta = number_random_gt_0();
        shorten(&alpha, &beta);

        long computed_period_length = lambda(alpha, beta, omega.numerator, omega.denominator, X_MIN, X_MAX, dx);

        if (computed_period_length == NO_PERIOD)
        {
            printf("No period found for a = %lld/%lld and omaga = %lld/%lld! Trying 10*XMAX!\n", alpha, beta, omega.numerator, omega.denominator);
            computed_period_length = lambda(alpha, beta, omega.numerator, omega.denominator, X_MIN, 10 * X_MAX, dx);

            if (computed_period_length == NO_PERIOD)
            {
                printf("Still no period for X_MAX * 10!\n");
                continue;
            }
        }
        else if (computed_period_length == ARRAY_SIZE_EXCEEDED)
        {
            printf("Array size exceeded for a = %lld/%lld and omaga = %lld/%lld!\n", alpha, beta, omega.numerator, omega.denominator);
            continue;
        }
        else if (computed_period_length == DX_LENGTH_TO_SMALL)
        {
            printf("Too many elements cut from dx for a = %lld/%lld and omaga = %lld/%lld! Trying 10*X_MAX!\n", alpha, beta, omega.numerator, omega.denominator);
            computed_period_length = lambda(alpha, beta, omega.numerator, omega.denominator, X_MIN, 10 * X_MAX, dx);

            if (computed_period_length == DX_LENGTH_TO_SMALL)
            {
                printf("Still too many elements cut from dx for X_MAX * 10!\n");
                continue;
            }
        }
        else
        {
            switch (conjecture)
            {
            case CONJECTURE_2_1:
                // lambda < alpha + beta + 1 for omega in (0, 1)
                if (!(computed_period_length < alpha + beta + 1))
                {
                    printf("Assertion for conjecture 2.1 (lambda < alpha + beta + 1 for omega in (0, 1)) for a = %lld/%lld, omaga = %lld/%lld and lambda = %ld!\n", alpha, beta, omega.numerator, omega.denominator, computed_period_length);
                }
                break;

            case CONJECTURE_2_2:
                // lambda < alpha + beta + 1 for omega in (0, 1) and near 1
                if (!(computed_period_length < alpha + beta + 1))
                {
                    printf("Assertion for conjecture 2.2 (lambda < alpha + beta + 1 for omega in (0, 1) and near 1) for a = %lld/%lld, omaga = %lld/%lld and lambda = %ld!\n", alpha, beta, omega.numerator, omega.denominator, computed_period_length);
                }
                break;

            case CONJECTURE_3_0:
                // lambda = alpha + beta + 1 for omega = 1
                if (!(computed_period_length == alpha + beta + 1))
                {
                    printf("Assertion for conjecture 3 (lambda = alpha + beta + 1 for omega = 1) for a = %lld/%lld, omaga = %lld/%lld and lambda = %ld!\n", alpha, beta, omega.numerator, omega.denominator, computed_period_length);
                }
                break;

            case CONJECTURE_4_1:
                // lambda >= alpha + beta + 1 for omega in (1, 2)
                if (!(computed_period_length >= alpha + beta + 1))
                {
                    printf("Assertion for conjecture 4.1 (lambda >= alpha + beta + 1 for omega in (1, 2)) for a = %lld/%lld, omaga = %lld/%lld and lambda = %ld!\n", alpha, beta, omega.numerator, omega.denominator, computed_period_length);
                }
                break;

            case CONJECTURE_4_2:
                // lambda >= alpha + beta + 1 for omega in (1, 2) and near 1
                if (!(computed_period_length >= alpha + beta + 1))
                {
                    printf("Assertion for conjecture 4.2 (lambda >= alpha + beta + 1 for omega in (1, 2) and near 1) for a = %lld/%lld, omaga = %lld/%lld and lambda = %ld!\n", alpha, beta, omega.numerator, omega.denominator, computed_period_length);
                }
                break;

            case CONJECTURE_5_0:
                // lambda > alpha + beta + 1 for omega >= 2
                if (!(computed_period_length > alpha + beta + 1))
                {
                    printf("Assertion for conjecture 5 (lambda > alpha + beta + 1 for omega > 2) for a = %lld/%lld, omaga = %lld/%lld and lambda = %ld!\n", alpha, beta, omega.numerator, omega.denominator, computed_period_length);
                }
                break;

            case CONJECTURE_6_1:
                // lambda is about gamma/delta * (alpha + beta + 1)
                mean_observed += (double)computed_period_length;
                break;

            case CONJECTURE_6_2:
                // lambda is about gamma/delta * (alpha + beta + 1)
                // prediction = rational_to_double(omega) * (alpha + beta + 1) - 0.00038130731262425493 * (omega.numerator - omega.denominator);
                prediction = floor(rational_to_double(omega) * (alpha + beta + 1));
                prediction += 0.654464 * sin(0.184608 + gamma - delta);
                error = prediction - computed_period_length;
                ss_res += error * error;
                ss_tot_part = prediction - mean_observed / number_of_tests;
                ss_tot += ss_tot_part;
                break;

            default:
                break;
            }
        }
    }

    if (conjecture == CONJECTURE_6_1)
    {
        printf("Mean observed: %f\n", mean_observed / number_of_tests);
    }
    else if (conjecture == CONJECTURE_6_2)
    {
        double r_squared = 1 - ss_res / ss_tot;
        printf("R^2 = %f\n", r_squared);
        if (r_squared < 0.9)
        {
            printf("R^2 is too low!\n");
        }
    }
}

/**
 * Wrapper function for testing conjectures.
 *
 * @param *dx The pointer to the array that will hold the dx values.
 */
void test_conjectures(number_t *dx)
{
    int conjecture = CONJECTURE_2_1 | CONJECTURE_2_2 | CONJECTURE_3_0 | CONJECTURE_4_1 | CONJECTURE_4_2 | CONJECTURE_4_3 | CONJECTURE_5_0 | CONJECTURE_6_1 | CONJECTURE_6_2;
    // conjecture = CONJECTURE_6_1 | CONJECTURE_6_2;

    for (Conjecture c = CONJECTURE_2_1; c <= CONJECTURE_6_2; c = (Conjecture)(c << 1))
    {
        if (conjecture & c)
        {
            test_concjeture2_to_6(dx, c, NUMBER_OF_TESTS);
        }
    }
}
