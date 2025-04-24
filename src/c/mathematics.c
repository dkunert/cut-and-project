#include <stdbool.h>
#include <time.h>
#include "mathematics.h"

/**
 * Finds the period length of the sequence defined by alpha, beta, gamma and delta
 * (a = alpha/beta, omega = gamma/delta.) in the interval [x_min, x_max].
 *
 * @param alpha The numerator of a.
 * @param beta The denominator of a.
 * @param gamma The numerator of omega.
 * @param delta The denominator of omaga.
 * @param x_min The minimum value of x.
 * @param x_max The maximum value of x.
 * @param dx The pointer to the array that will hold the dx values.
 * @return The period length of the sequence or ARRAY_SIZE_EXCEEDED
 *         if the array size is exceeded or DX_LENGTH_TO_SMALL if too 
 *         many elements are cut from dx.
 */
long lambda(number_t alpha, number_t beta, number_t gamma, number_t delta,
            const number_t x_min, const number_t x_max, number_t *dx)
{
    // Shorten the fractions alpha/beta and gamma/delta optaining smaller figures.
    shorten(&alpha, &beta);
    shorten(&gamma, &delta);

    const number_t alpha_delta_xmin = alpha * delta * x_min;
    const number_t beta_delta = beta * delta;
    rational_t l = rational_create(alpha_delta_xmin - alpha * gamma, beta_delta);
    rational_t u = rational_create(alpha_delta_xmin + beta * gamma, beta_delta);
    const rational_t to_add = rational_create(alpha, beta);

    // Calculate the initial dx values, i.e. the projected x values.
    number_t x = x_min;
    long int index_dx = 0;
    number_t beta_x = beta * x;
    bool is_not_first = false;

    while (x < x_max)
    {
        const number_t y_ceil_l = rational_ceil(l);
        const number_t y_floor_u = rational_floor(u);
        const number_t elements_to_add = y_floor_u - y_ceil_l + 1;
        if (index_dx + elements_to_add >= MAX_PERIOD_ARRAY_SIZE)
        {
            return ARRAY_SIZE_EXCEEDED;
        }

        number_t current_dx = beta_x + alpha * y_ceil_l;

        for (int i = 0; i < elements_to_add; i++)
        {
            if (is_not_first)
            {
                dx[index_dx - 1] -= current_dx;
            }
            else
            {
                is_not_first = true;
            }
            dx[index_dx++] = current_dx;
            current_dx += alpha;
        }

        beta_x += beta;
        l = rational_add(l, to_add);
        u = rational_add(u, to_add);
        x++;
    }

    // Find the period length.
    long index_start = 1;
    long index_end = index_dx - 1;
    const long initial_dx_length = index_end - index_start + 1;
    long current_dx_length = initial_dx_length;
    long period_length = NO_PERIOD;
    while (period_length == NO_PERIOD)
    {
        index_start++;
        index_end--;
        current_dx_length -= 2;
        if (((double)current_dx_length / (double)initial_dx_length) < FRACTION_OF_REMAINING_ELEMENTS)
        {
            period_length = DX_LENGTH_TO_SMALL;
            break;
        }
        if (index_start >= index_end)
            break;
        period_length = find_period_length(index_start, index_end, dx);
    }

    return period_length;
}

static bool random_is_initilazed = false;

/**
 * Generates a random number between min and max, inclusive.
 * The function initializes the random number generator if it hasn't been initialized yet.
 * It also checks if min is greater than max and exits with an error message if so.
 *
 * @param min The minimum value (inclusive).
 * @param max The maximum value (inclusive).
 * @return A random number between min and max, inclusive.
 */
number_t random_number_including(const number_t min, const number_t max)
{
    if (!random_is_initilazed)
    {
        srand((unsigned int)time(NULL));
        random_is_initilazed = true;
    }

    if (min > max)
    {
        fprintf(stderr, "Error: min is greater than max.\n");
        exit(EXIT_FAILURE);
    }

    const number_t range = max - min + 1;
    number_t random_number = min + (number_t)(rand() % range);
    return random_number;
}

/**
 * Generates a random rational number greater than 0.
 *
 * @param lt_1 A rational number less than 1 is created if true.
 *             A rational number greater than 1 is created if false.
 * @return A random rational number greater than 0.
 */
rational_t rational_random_gt_0(const bool lt_1)
{
    number_t a, b;

    do
    {
        // Random values between 1 and MAX_RANDOM
        a = random_number_including(1, MAX_RANDOM);
        b = random_number_including(1, MAX_RANDOM);
    } while (a == b);

    if (lt_1)
    {
        return rational_create(MIN(a, b), MAX(a, b));
    }
    else
    {
        return rational_create(MAX(a, b), MIN(a, b));
    }
}

/**
 * Generates random rational greter than 0
 * an less than 1.
 *
 * @return A random rational in (1, MAX_RAMDOM].
 */
rational_t rational_random_gt_0_lt_1(void)
{
    return rational_random_gt_0(true);
}

/**
 * Generates random rational greter than 1.
 *
 * @return A random rational in (1, MAX_RAMDOM].
 */
rational_t rational_random_gt_1(void)
{
    return rational_random_gt_0(false);
}

/**
 * Generates random rational greater or equal 2
 *
 * @return A random rational in [2, MAX_RAMDOM].
 */
rational_t rational_random_ge_2(void)
{
    number_t a, b;

    do
    {
        // Random values in [1, MAX_RANDOM]
        a = random_number_including(1, MAX_RANDOM);
        b = random_number_including(1, MAX_RANDOM);
    } while (a < 2 * b);

    return rational_create(a, b);
}

/**
 * Generates a random number greater than 0.
 *
 * @return A random number in (0, MAX_RANDOM].
 */
number_t number_random_gt_0(void)
{
    return random_number_including(1, MAX_RANDOM);
}
