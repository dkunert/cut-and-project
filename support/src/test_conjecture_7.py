"""
Tests conjecture 7 against observed period lengths stored in a CSV file.

The CSV must have the header "o_n,o_d,a_n,a_d,period" and one data row per line.
For each row, computes
    N = floor(o_n * alpha / o_d) + floor(o_n * beta / o_d) + 1
    D = alpha^2 + beta^2
and checks that the observed period equals N if D does not divide N,
else N / D.
"""

import csv
import sys

CSV_PATH = "../../tests/new_find_patterns_x_max_1000000_51012_lines.csv"


def test_conjecture_7_from_csv(path: str) -> int:
    total = 0
    mismatches = 0
    count_divides = 0      # rows where D | N  (degenerate branch: lambda = N/D)
    count_not_divides = 0  # rows where D does not divide N (generic branch: lambda = N)

    with open(path, newline="") as f:
        reader = csv.reader(f)
        next(reader)  # skip header

        for row in reader:
            o_n, o_d, a_n, a_d, period = (int(x) for x in row)
            alpha, beta = a_n, a_d

            N = (o_n * alpha) // o_d + (o_n * beta) // o_d + 1
            D = alpha * alpha + beta * beta

            if N % D == 0:
                count_divides += 1
                expected = N // D
            else:
                count_not_divides += 1
                expected = N

            total += 1
            if expected != period:
                mismatches += 1
                if mismatches <= 10:
                    print(
                        f"Mismatch: omega = {o_n}/{o_d}, alpha = {alpha}, "
                        f"beta = {beta}, N = {N}, D = {D}, "
                        f"expected = {expected}, observed period = {period}"
                    )

    print(
        f"Conjecture 7 test from CSV '{path}': "
        f"{total} rows checked, {mismatches} mismatches."
    )
    print(f"  Branch coverage: D | N       (lambda = N/D): {count_divides} rows")
    print(f"                   D does not divide N (lambda = N  ): {count_not_divides} rows")
    return mismatches


if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else CSV_PATH
    sys.exit(1 if test_conjecture_7_from_csv(path) > 0 else 0)
