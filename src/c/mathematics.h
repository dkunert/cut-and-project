#ifndef MATHEMATICS_H
#define MATHEMATICS_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include "constants.h"

typedef int_fast64_t number_t;

/**
 * Allocates aligned memory for an array of number_t.
 * The allocated memory is aligned to 16 bytes.
 * Returns a pointer to the allocated memory.
 *
 * @param number_of_elements The number of elements.
 * @return A pointer to the allocated memory.
 */
static inline number_t *dx_alloc(size_t number_of_elements)
{
    number_t *ptr = NULL;
    if (posix_memalign((void **)&ptr, 16, number_of_elements * sizeof(number_t)) != 0)
    {
        fprintf(stderr, "Error: Failed to allocate aligned memory.\n");
        exit(EXIT_FAILURE);
    }

    size_t total_bytes = MAX_PERIOD_ARRAY_SIZE * sizeof(number_t);
    double total_mb = total_bytes / (1024.0 * 1024.0);
    printf("Allocated %.2f MB for dx\n", total_mb);

    return ptr;
}

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MAX(a, b) ((a) > (b) ? (a) : (b))

/**
 * Returns the greatest common divisor (GCD) of two numbers.
 * The GCD is calculated using the Euclidean algorithm.
 *
 * @param a The first number.
 * @param b The second number.
 * @return The GCD of a and b.
 */
static inline number_t gcd(number_t a, number_t b)
{
    while (b != 0)
    {
        const number_t r = a % b;
        a = b;
        b = r;
    }
    return a;
}

/**
 * Shortens two numbers by dividing them by their GCD.
 *
 * @param a Pointer to the first number.
 * @param b Pointer to the second number.
 */
static inline void shorten(number_t *a, number_t *b)
{
    const number_t g = gcd(*a, *b);
    *a /= g;
    *b /= g;
}

/**
 * Returns the least common multiple (LCM) of two numbers.
 * The LCM is calculated using the formula: lcm(a, b) = (a / gcd(a, b)) * b.
 *
 * @param a The first number.
 * @param b The second number.
 * @return The LCM of a and b.
 */
static inline number_t lcm(const number_t a, const number_t b)
{
    return (a / gcd(a, b)) * b;
}

/**
 * A rational number is represented as a pair of integers (numerator, denominator).
 * The denominator is always positive.
 */
typedef struct
{
    number_t numerator;
    number_t denominator;
} rational_t;

/**
 * Creates a rational number from a numerator and denominator.
 * The denominator must not be zero. If it is, the program will exit with an error.
 * The resulting rational number has a positve denominator and is simplified to
 * its lowest terms.
 *
 * @param numerator The numerator of the rational number.
 * @param denominator The denominator of the rational number.
 * @return A rational number represented as a struct.
 * @note The denominator must not be zero. If it is, the program will exit with an error.
 */
static inline rational_t rational_create(number_t numerator, number_t denominator)
{
    if (denominator == 0)
    {
        fprintf(stderr, "Error: denominator cannot be zero.\n");
        exit(EXIT_FAILURE);
    }

    // Simplify the rational
    const number_t g = gcd(numerator, denominator);
    numerator /= g;
    denominator /= g;

    // Ensure denominator is positive
    if (denominator > 0)
    {
        return (rational_t){numerator, denominator};
    }
    else
    {
        return (rational_t){-numerator, -denominator};
    }
}

/**
 * Add two rational numbers.
 * The result is simplified to its lowest terms.
 *
 * @param x The first rational number.
 * @param y The second rational number.
 * @return The sum of the two rational numbers.
 */
static inline rational_t rational_add(const rational_t x, const rational_t y)
{
    // Scale factors
    const number_t _lcm = lcm(x.denominator, y.denominator);
    const number_t scale_x = _lcm / x.denominator;
    const number_t scale_y = _lcm / y.denominator;
    return (rational_t){x.numerator * scale_x + y.numerator * scale_y, _lcm};
}

/**
 * Substract two rational numbers.
 * The result is simplified to its lowest terms.
 *
 * @param x The first rational number.
 * @param y The second rational number.
 * @return The difference of the two rational numbers.
 */
static inline rational_t rational_subtract(const rational_t x, const rational_t y)
{
    return rational_add(x, (rational_t){-y.numerator, y.denominator});
}

/**
 * Returns floor(r.num / r.den) as number_t.
 *
 * For positive rationals, integer division is already floor.
 * For negative rationals, if there's a nonzero remainder, subtract 1.
 *
 * @param r The rational number.
 * @return The floored value of the rational number.
 */
static inline number_t rational_floor(const rational_t r)
{
    // Truncated division
    const number_t div = r.numerator / r.denominator;

    // If remainder != 0 and r is negative, subtract 1 for true floor
    return (r.numerator % r.denominator != 0 && r.numerator < 0) ? div - 1 : div;
}

/**
 * Returns ceil(r.num / r.den) as number_t.
 *
 * For negative rationals, integer division is already ceil.
 * For positive rationals, if there's a nonzero remainder, add 1.
 *
 * @param r The rational number.
 * @return The ceiled value of the rational number.
 */
static inline number_t rational_ceil(const rational_t r)
{
    // Truncated division
    const number_t div = r.numerator / r.denominator;

    // If remainder != 0 and r is positive, add 1 for true ceil
    return (r.numerator % r.denominator != 0 && r.numerator > 0) ? div + 1 : div;
}

/**
 * Converts a rational number to a double.
 *
 * @param r The rational number.
 * @return The double representation of the rational number.
 */
static inline double rational_to_double(const rational_t r)
{
    return (double)r.numerator / (double)r.denominator;
}

/**
 * Finds the period length of a sequence defined by dx between elements
 * index_start and index_max (both including).
 * It uses a brute-force approach.
 *
 * @param index_start The starting index of the sequence.
 * @param index_end The ending index of the sequence.
 * @param dx The array of numbers.
 * @return The period length of the sequence or NO_PERIOD if no period is found.
 */
static long find_period_length(const long index_start, const long index_end, const number_t *dx)
{
    const long n = index_end - index_start + 1;
    if (n < 2)
        return NO_PERIOD;

    // Try each candidate period length
    for (long period = 1; period <= n / 2; period++)
    {
        // Early checks: compare the last element with the element at index (n-1) % p.
        if (dx[n - 1] != dx[(n - 1) % period])
            continue;

        // Check if the sequence is periodic with period p.
        size_t count = index_end - period - index_start + 1;
        if (memcmp(&dx[index_start], &dx[index_start + period],
                   count * sizeof(number_t)) == 0)
            return period;
    }

    return NO_PERIOD;
}

/**
 * Checks if the period length is legal, i.e. greater than 0.
 *
 * @param period_length The period length to check.
 * @return true if the period length is legal, false otherwise.
 */
static inline bool is_legal_period_length(long period_length)
{
    return period_length > 0;
}

/**
 * Compares two number_t values for sorting.
 * Returns negative if x < y, zero if x == y, positive if x > y.
 *
 * @param p Pointer to the first number_t value.
 * @param q Pointer to the second number_t value.
 * @return The comparison result.
 */
static inline int cmp_int_fast64(const void *p, const void *q) {
    number_t x = *(const number_t*)p;
    number_t y = *(const number_t*)q;
    // return negative if x<y, zero if x==y, positive if x>y
    return (x > y) - (x < y);
}

/**
 * Sorts a range of elements in an array using qsort.
 * The range is defined by the indices a and b (inclusive).
 *
 * @param array The array to sort.
 * @param a The starting index of the range.
 * @param b The ending index of the range.  
 */
void inline sort_range(number_t *array, size_t a, size_t b) {
    if (b < a) return;                     // nothing to do
    size_t count = b - a + 1;              // number of elements
    qsort(array + a,                      // start at &array[a]
          count,                          // how many elements
          sizeof *array,                  // size of each element
          cmp_int_fast64);                // your comparator
}

// Function prototypes
long lambda(number_t alpha, number_t beta, number_t gamma, number_t delta, number_t x_min, number_t x_max, bool sort, number_t *dx);
number_t random_number_including(const number_t min, const number_t max);
rational_t rational_random_gt_0_lt_1(void);
rational_t rational_random_gt_1(void);
rational_t rational_random_ge_2(void);
number_t number_random_gt_0(void);

#endif /* MATHEMATICS_H */
