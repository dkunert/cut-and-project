#!/usr/bin/env python3
"""
Recompute set-valued periods for CSV rows where the C-side run aborted
and stored a negative sentinel (-2/-3/-4) in `period_set`.

The set period is computed *directly from the residue model*, independently
of the theorem the paper proves:

    1. Form the N residues  c_r = (- alpha * beta^{-1} * r) mod D
       for r = -floor(beta*omega), ..., floor(alpha*omega).
    2. Sort them.  The set of projected values within one length-D window
       on the tilde-p axis is exactly this sorted residue list, so the
       set-valued gap sequence is a length-N cyclic gap sequence with
       sum D.
    3. The set-valued period is the minimal positive divisor of N for
       which the gap sequence repeats with that period.

This is mathematically independent of Theorem 4.6 (the set-period theorem):
the script does not assume lambda_set = N; it computes the minimal period
empirically from the residue gaps.

Usage:
    python3 recompute_broken_set_periods.py [csv_path ...]

Default: rewrites the three CSVs in tests/ in place.  Original values are
preserved for rows where period_set is non-negative; only negative-sentinel
rows are replaced.
"""

import csv
import os
import sys
from math import gcd

import numpy as np


def _divisors(n):
    out = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            out.append(i)
            if i != n // i:
                out.append(n // i)
        i += 1
    out.sort()
    return out


def set_period_from_residues(alpha: int, beta: int, omega_n: int, omega_d: int) -> int:
    """
    Compute the minimal set-valued period directly from the residue model.

    Memory: ~8*N bytes for the residue array (numpy int64).
    Time:   O(N log N) for the sort plus O(N * d(N)) worst-case for the
            period search, where d(N) is the divisor count of N.
    """
    D = alpha * alpha + beta * beta
    r_max = (omega_n * alpha) // omega_d
    r_min = -((omega_n * beta) // omega_d)
    N = r_max - r_min + 1
    assert N == (omega_n * alpha) // omega_d + (omega_n * beta) // omega_d + 1

    # multiplier m = (- alpha * beta^{-1}) mod D
    beta_inv = pow(beta, -1, D)
    m = (-alpha * beta_inv) % D

    # residues c_r = (m * r) mod D for r = r_min, ..., r_max
    r = np.arange(r_min, r_max + 1, dtype=np.int64)
    residues = (m * r) % D

    # set-valued: deduplicate before computing gaps
    distinct = np.unique(residues)  # sorted by construction
    K = len(distinct)

    # cyclic gap sequence of length K, summing to D
    gaps = np.empty(K, dtype=np.int64)
    gaps[:-1] = distinct[1:] - distinct[:-1]
    gaps[-1] = distinct[0] + D - distinct[-1]

    # minimal period divides K; try divisors in increasing order
    for p in _divisors(K):
        if p == K:
            return K
        block = gaps[:p]
        reshaped = gaps.reshape(K // p, p)
        if np.array_equal(reshaped, np.broadcast_to(block, reshaped.shape)):
            return int(p)
    return K  # unreachable: K is always a period


def recompute_csv(path: str) -> tuple[int, int]:
    """
    Returns (n_recomputed, n_total).
    Rewrites the file in place if any rows were changed.
    """
    with open(path, newline="") as f:
        reader = csv.reader(f)
        header = next(reader)
        rows = list(reader)

    if header != ["o_n", "o_d", "a_n", "a_d", "period_multiset", "period_set"]:
        raise ValueError(f"unexpected header in {path}: {header}")

    changed = 0
    for i, row in enumerate(rows):
        on, od, a, b, pm, ps = (int(x) for x in row)
        if ps < 0:
            new_ps = set_period_from_residues(a, b, on, od)
            rows[i] = [str(on), str(od), str(a), str(b), str(pm), str(new_ps)]
            changed += 1
            print(f"  {os.path.basename(path)} row {i+2}: "
                  f"a={a}, b={b}, w={on}/{od} -> period_set = {new_ps} "
                  f"(was {ps})", flush=True)

    if changed:
        tmp = path + ".tmp"
        with open(tmp, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(header)
            writer.writerows(rows)
        os.replace(tmp, path)

    return changed, len(rows)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    tests_dir = os.path.normpath(os.path.join(here, "..", "..", "tests"))
    default_paths = [
        os.path.join(tests_dir, "multiset_and_set_new_find_patterns_51012_lines.csv"),
        os.path.join(tests_dir, "multiset_and_set_degenerate_patterns_5000_lines.csv"),
        os.path.join(tests_dir, "set_theorem_balanced_test.csv"),
    ]
    paths = sys.argv[1:] if len(sys.argv) > 1 else default_paths

    total_changed = 0
    total_rows = 0
    for p in paths:
        print(f"\nProcessing {p} ...")
        changed, total = recompute_csv(p)
        print(f"  -> {changed} row(s) recomputed out of {total}")
        total_changed += changed
        total_rows += total

    print(f"\nDone: {total_changed} row(s) recomputed across {total_rows} total.")


if __name__ == "__main__":
    main()
