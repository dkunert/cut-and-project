#!/usr/bin/env python3
"""
Verify the paper's claims against the CSV data in tests/.

Checks, for every row:
  * Theorem 3.1 (multiset period):
        lambda_multiset = N        if D does not divide N
                        = N / D    if D divides N
  * Theorem 4.6 (set-valued period):
        lambda_set = N             if N <  D
                   = 1             if N >= D
  * Corollary 5.1 (finiteness):    lambda_multiset > 0  and  lambda_set > 0
  * Corollary 5.2 (omega = 1):     lambda_multiset = alpha + beta + 1
  * Corollary 5.3 (0 < omega < 1): lambda_multiset < alpha + beta + 1
  * Corollary 5.4 (1 < omega < 2,  D nmid N): lambda_multiset >= alpha + beta + 1
  * Corollary 5.5 (omega > 2,      D nmid N): lambda_multiset >  alpha + beta + 1

The CSVs use the six-column format
    o_n, o_d, a_n, a_d, period_multiset, period_set
where (o_n / o_d) = omega and (a_n, a_d) = (alpha, beta).

Negative period_set values are reported separately (sentinel error codes
emitted by aborted C-side runs).  The expected value from the theorem is
also printed for any negative-sentinel row, so the user can patch the
CSV if needed.

Pure standard library; no third-party dependencies.
"""

import csv
import os
import sys
from fractions import Fraction


def verify_csv(path: str) -> dict:
    print(f"\n{'=' * 70}")
    print(f"Verifying: {path}")
    print(f"{'=' * 70}")

    total = 0
    multi_mismatches = 0
    set_mismatches = 0
    set_negative_sentinels = 0
    finiteness_violations = 0

    cor_omega1_tested = cor_omega1_pass = 0
    cor_small_tested = cor_small_pass = 0
    cor_medium_tested = cor_medium_pass = 0
    cor_large_tested = cor_large_pass = 0

    count_divides = count_not_divides = 0
    count_n_lt_d = count_n_ge_d = 0

    with open(path, newline="") as f:
        reader = csv.reader(f)
        header = next(reader)
        if header != ["o_n", "o_d", "a_n", "a_d", "period_multiset", "period_set"]:
            raise ValueError(f"Unexpected header in {path}: {header}")

        for row in reader:
            o_n, o_d, alpha, beta, period_multi, period_set = (int(x) for x in row)
            omega = Fraction(o_n, o_d)
            N = (o_n * alpha) // o_d + (o_n * beta) // o_d + 1
            D = alpha * alpha + beta * beta
            Lambda = alpha + beta + 1

            expected_multi = N if N % D != 0 else N // D
            expected_set = N if N < D else 1

            if N % D == 0:
                count_divides += 1
            else:
                count_not_divides += 1
            if N < D:
                count_n_lt_d += 1
            else:
                count_n_ge_d += 1
            total += 1

            if expected_multi != period_multi:
                multi_mismatches += 1
                if multi_mismatches <= 5:
                    print(f"  Multiset MISMATCH: omega={o_n}/{o_d} a={alpha} b={beta} "
                          f"N={N} D={D} expected={expected_multi} got={period_multi}")

            if period_set < 0:
                set_negative_sentinels += 1
                if set_negative_sentinels <= 5:
                    print(f"  Set sentinel:      omega={o_n}/{o_d} a={alpha} b={beta} "
                          f"N={N} D={D} expected={expected_set} got={period_set}")
            elif expected_set != period_set:
                set_mismatches += 1
                if set_mismatches <= 5:
                    print(f"  Set MISMATCH:      omega={o_n}/{o_d} a={alpha} b={beta} "
                          f"N={N} D={D} expected={expected_set} got={period_set}")

            if period_multi <= 0:
                finiteness_violations += 1

            if omega == 1:
                cor_omega1_tested += 1
                if period_multi == Lambda:
                    cor_omega1_pass += 1
            if 0 < omega < 1:
                cor_small_tested += 1
                if period_multi < Lambda:
                    cor_small_pass += 1
            if 1 < omega < 2 and N % D != 0:
                cor_medium_tested += 1
                if period_multi >= Lambda:
                    cor_medium_pass += 1
            if omega > 2 and N % D != 0:
                cor_large_tested += 1
                if period_multi > Lambda:
                    cor_large_pass += 1

    print(f"\nTotal rows: {total}")
    print(f"  D | N: {count_divides}    D nmid N: {count_not_divides}")
    print(f"  N < D: {count_n_lt_d}    N >= D: {count_n_ge_d}")
    print()
    print(f"--- Multiset (Theorem 3.1) ---")
    print(f"  Mismatches: {multi_mismatches} / {total}")
    print(f"--- Set (Theorem 4.6) ---")
    print(f"  Mismatches:        {set_mismatches} / {total}")
    print(f"  Negative sentinel: {set_negative_sentinels} / {total}")
    print(f"--- Finiteness ---")
    print(f"  Violations: {finiteness_violations} / {total}")

    def report(label, n_pass, n_test):
        status = "(no qualifying rows)" if n_test == 0 else f"{n_pass}/{n_test}"
        print(f"  {label}: {status}")

    print(f"--- Corollaries ---")
    report("5.2 (omega=1)            ", cor_omega1_pass, cor_omega1_tested)
    report("5.3 (0<omega<1)          ", cor_small_pass, cor_small_tested)
    report("5.4 (1<omega<2, D nmid N)", cor_medium_pass, cor_medium_tested)
    report("5.5 (omega>2,   D nmid N)", cor_large_pass, cor_large_tested)

    return {
        "total": total,
        "multi_mismatches": multi_mismatches,
        "set_mismatches": set_mismatches,
        "set_negative_sentinels": set_negative_sentinels,
    }


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    tests_dir = os.path.normpath(os.path.join(here, "..", "..", "tests"))
    default_paths = [
        os.path.join(tests_dir, "multiset_and_set_new_find_patterns_51012_lines.csv"),
        os.path.join(tests_dir, "multiset_and_set_degenerate_patterns_5000_lines.csv"),
        os.path.join(tests_dir, "set_theorem_balanced_test.csv"),
    ]
    paths = sys.argv[1:] if len(sys.argv) > 1 else default_paths

    grand_total = 0
    grand_multi = 0
    grand_set = 0
    grand_neg = 0
    for p in paths:
        r = verify_csv(p)
        grand_total += r["total"]
        grand_multi += r["multi_mismatches"]
        grand_set += r["set_mismatches"]
        grand_neg += r["set_negative_sentinels"]

    print()
    print("=" * 70)
    print(f"AGGREGATE OVER {len(paths)} FILE(S)")
    print("=" * 70)
    print(f"  Total rows:                {grand_total}")
    print(f"  Multiset mismatches:       {grand_multi}")
    print(f"  Set mismatches:            {grand_set}")
    print(f"  Set negative sentinels:    {grand_neg}")
    print()
    if grand_multi == 0 and grand_set == 0 and grand_neg == 0:
        print("ALL CHECKS PASSED.")
        sys.exit(0)
    else:
        print("FAILURES PRESENT.")
        sys.exit(1)


if __name__ == "__main__":
    main()
