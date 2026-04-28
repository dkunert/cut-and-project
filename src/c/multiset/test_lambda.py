"""
Python reimplementation of the C lambda() function for testing.
Computes the period length of a cut-and-project sequence.

Usage:
    python3 test_lambda.py <alpha> <beta> <gamma> <delta> [--x_max N] [--sort] [--debug]

Examples:
    python3 test_lambda.py 2 1 3 1              # paper example: alpha=2, beta=1, omega=3
    python3 test_lambda.py 1 2 3 1              # swapped: alpha=1, beta=2, omega=3
    python3 test_lambda.py 2 1 3 1 --debug      # show dx array
    python3 test_lambda.py 2 1 3 1 --x_max 100  # smaller x range
"""

import sys
from fractions import Fraction
from math import ceil, floor, gcd


def find_period_length(dx, index_start, index_end):
    n = index_end - index_start + 1
    if n < 2:
        return None

    for period in range(1, n // 2 + 1):
        if dx[index_end] != dx[index_start + (n - 1) % period]:
            continue
        match = True
        for i in range(index_start, index_end - period + 1):
            if dx[i] != dx[i + period]:
                match = False
                break
        if match:
            return period
    return None


def lambda_period(alpha, beta, gamma, delta, x_min=0, x_max=10000,
                  sort_mode=False, fraction_remaining=0.9):
    g = gcd(alpha, beta)
    alpha, beta = alpha // g, beta // g
    g = gcd(gamma, delta)
    gamma, delta = gamma // g, delta // g

    beta_delta = beta * delta
    l = Fraction(alpha * delta * x_min - alpha * gamma, beta_delta)
    u = Fraction(alpha * delta * x_min + beta * gamma, beta_delta)
    to_add = Fraction(alpha, beta)

    dx = []
    beta_x = beta * x_min
    is_not_first = False

    for x in range(x_min, x_max):
        y_ceil_l = ceil(l)
        y_floor_u = floor(u)
        elements_to_add = y_floor_u - y_ceil_l + 1

        if elements_to_add > 0:
            current_dx = beta_x + alpha * y_ceil_l

            for i in range(elements_to_add):
                if not sort_mode:
                    if is_not_first:
                        dx[-1] -= current_dx
                    else:
                        is_not_first = True

                dx.append(current_dx)
                current_dx += alpha

        beta_x += beta
        l += to_add
        u += to_add

    if sort_mode:
        dx.sort()
        dx = [dx[i + 1] - dx[i] for i in range(len(dx) - 1)]

    if sort_mode:
        to_delete = int((1.0 - fraction_remaining) / 40.0 * len(dx))
    else:
        to_delete = 1

    index_start = to_delete
    index_end = len(dx) - 1 - to_delete
    initial_length = index_end - index_start + 1
    current_length = initial_length
    period = None

    while period is None:
        index_start += 1
        index_end -= 1
        current_length -= 2
        if current_length / initial_length < fraction_remaining:
            break
        if index_start >= index_end:
            break
        period = find_period_length(dx, index_start, index_end)

    return period, dx


def main():
    args = sys.argv[1:]

    if len(args) < 4:
        print(__doc__)
        sys.exit(1)

    alpha = int(args[0])
    beta = int(args[1])
    gamma = int(args[2])
    delta = int(args[3])

    x_max = 10000
    sort_mode = False
    debug = False

    i = 4
    while i < len(args):
        if args[i] == "--x_max" and i + 1 < len(args):
            x_max = int(args[i + 1])
            i += 2
        elif args[i] == "--sort":
            sort_mode = True
            i += 1
        elif args[i] == "--debug":
            debug = True
            i += 1
        else:
            print(f"Unknown argument: {args[i]}")
            sys.exit(1)

    g_ab = gcd(alpha, beta)
    a_red, b_red = alpha // g_ab, beta // g_ab
    g_gd = gcd(gamma, delta)
    g_red, d_red = gamma // g_gd, delta // g_gd
    omega = Fraction(gamma, delta)

    N = floor(omega * a_red) + floor(omega * b_red) + 1
    D = a_red * a_red + b_red * b_red

    print(f"alpha = {a_red}, beta = {b_red}, omega = {g_red}/{d_red}")
    print(f"N = {N}, D = {D}")
    print(f"D divides N: {N % D == 0}")
    if N % D == 0:
        print(f"Conjecture 7 predicts: lambda = N/D = {N // D}")
    else:
        print(f"Conjecture 7 predicts: lambda = N = {N}")

    period, dx = lambda_period(alpha, beta, gamma, delta,
                               x_max=x_max, sort_mode=sort_mode)

    print(f"Computed period: {period}")
    print(f"dx length: {len(dx)}")

    if debug:
        max_show = min(len(dx), 200)
        print(f"dx[0:{max_show}] = {dx[:max_show]}")


if __name__ == "__main__":
    main()
