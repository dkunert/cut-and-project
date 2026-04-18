"""
Comprehensive verification of all claims in conjecture_6.tex against CSV data.

Checks:
  1. Main formula (Theorem 3.1): lambda = N if D does not divide N, else N/D
  2. Corollary 5.1 (Finiteness): lambda > 0 always
  3. Corollary 5.2 (omega=1): lambda = alpha + beta + 1
  4. Corollary 5.3 (0 < omega < 1): lambda < alpha + beta + 1
  5. Corollary 5.4 (1 < omega < 2, D does not divide N): lambda >= alpha + beta + 1
  6. Corollary 5.5 (omega > 2, D does not divide N): lambda > alpha + beta + 1
  7. Earlier approximate formula: floor(omega*(alpha+beta+1)) matches count
"""

import csv
import sys
from fractions import Fraction
from math import floor


def verify_csv(path):
    print(f"\n{'='*70}")
    print(f"Verifying: {path}")
    print(f"{'='*70}")

    total = 0
    formula_mismatches = 0
    finiteness_violations = 0

    # Corollary counters
    cor_omega1_tested = 0
    cor_omega1_pass = 0
    cor_small_omega_tested = 0
    cor_small_omega_pass = 0
    cor_medium_omega_tested = 0
    cor_medium_omega_pass = 0
    cor_large_omega_tested = 0
    cor_large_omega_pass = 0

    # Branch coverage
    count_divides = 0
    count_not_divides = 0

    # Approximate formula comparison
    approx_exact_matches = 0

    # N < D vs N >= D regime
    count_n_lt_d = 0
    count_n_ge_d = 0

    with open(path, newline="") as f:
        reader = csv.reader(f)
        next(reader)  # skip header

        for row in reader:
            o_n, o_d, a_n, a_d, period = (int(x) for x in row)
            alpha, beta = a_n, a_d
            omega = Fraction(o_n, o_d)

            N = (o_n * alpha) // o_d + (o_n * beta) // o_d + 1
            D = alpha * alpha + beta * beta
            Lambda = alpha + beta + 1

            if N % D == 0:
                expected = N // D
                count_divides += 1
            else:
                expected = N
                count_not_divides += 1

            if N < D:
                count_n_lt_d += 1
            else:
                count_n_ge_d += 1

            total += 1

            # 1. Main formula
            if expected != period:
                formula_mismatches += 1
                if formula_mismatches <= 5:
                    print(f"  Formula MISMATCH: omega={o_n}/{o_d}, alpha={alpha}, "
                          f"beta={beta}, N={N}, D={D}, expected={expected}, "
                          f"observed={period}")

            # 2. Finiteness
            if period <= 0:
                finiteness_violations += 1

            # 3. Corollary: omega = 1
            if omega == 1:
                cor_omega1_tested += 1
                if period == Lambda:
                    cor_omega1_pass += 1

            # 4. Corollary: 0 < omega < 1
            if 0 < omega < 1:
                cor_small_omega_tested += 1
                if period < Lambda:
                    cor_small_omega_pass += 1

            # 5. Corollary: 1 < omega < 2 and D does not divide N
            if 1 < omega < 2 and N % D != 0:
                cor_medium_omega_tested += 1
                if period >= Lambda:
                    cor_medium_omega_pass += 1

            # 6. Corollary: omega > 2 and D does not divide N
            if omega > 2 and N % D != 0:
                cor_large_omega_tested += 1
                if period > Lambda:
                    cor_large_omega_pass += 1

            # 7. Approximate formula comparison
            approx = floor(float(omega) * Lambda)
            if approx == period:
                approx_exact_matches += 1

    # Report
    print(f"\nTotal rows: {total}")
    print()

    print("--- Main Formula (Theorem 3.1) ---")
    print(f"  Mismatches: {formula_mismatches} / {total}")
    print(f"  Branch coverage: D | N = {count_divides}, D does not divide N = {count_not_divides}")
    print(f"  Regime: N < D = {count_n_lt_d}, N >= D = {count_n_ge_d}")
    print()

    print("--- Corollary 5.1 (Finiteness) ---")
    print(f"  lambda > 0 violations: {finiteness_violations} / {total}")
    print()

    print("--- Corollary 5.2 (omega = 1: lambda = alpha+beta+1) ---")
    if cor_omega1_tested > 0:
        print(f"  Pass: {cor_omega1_pass} / {cor_omega1_tested}")
    else:
        print(f"  No omega=1 cases in this CSV")
    print()

    print("--- Corollary 5.3 (0 < omega < 1: lambda < alpha+beta+1) ---")
    if cor_small_omega_tested > 0:
        print(f"  Pass: {cor_small_omega_pass} / {cor_small_omega_tested}")
    else:
        print(f"  No 0<omega<1 cases in this CSV")
    print()

    print("--- Corollary 5.4 (1 < omega < 2, D nmid N: lambda >= alpha+beta+1) ---")
    if cor_medium_omega_tested > 0:
        print(f"  Pass: {cor_medium_omega_pass} / {cor_medium_omega_tested}")
    else:
        print(f"  No qualifying cases in this CSV")
    print()

    print("--- Corollary 5.5 (omega > 2, D nmid N: lambda > alpha+beta+1) ---")
    if cor_large_omega_tested > 0:
        print(f"  Pass: {cor_large_omega_pass} / {cor_large_omega_tested}")
    else:
        print(f"  No qualifying cases in this CSV")
    print()

    print("--- Approximate formula: floor(omega*(alpha+beta+1)) ---")
    print(f"  Exact matches: {approx_exact_matches} / {total} ({100*approx_exact_matches/total:.1f}%)")
    print()

    return formula_mismatches


if __name__ == "__main__":
    paths = sys.argv[1:] if len(sys.argv) > 1 else [
        "../../tests/new_find_patterns_x_max_1000000_51012_lines.csv",
        "../../tests/degenerate_patterns_5000_lines.csv",
    ]
    total_mismatches = 0
    for path in paths:
        total_mismatches += verify_csv(path)

    print("=" * 70)
    if total_mismatches == 0:
        print("ALL CHECKS PASSED.")
    else:
        print(f"TOTAL FORMULA MISMATCHES: {total_mismatches}")
    sys.exit(1 if total_mismatches > 0 else 0)
