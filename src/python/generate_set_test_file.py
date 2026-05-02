#!/usr/bin/env python3
"""
Generate a CSV test file with >= 100 rows each for N < D and N >= D,
to verify the set-period theorem: lambda_set = N if N<D, else 1.

Enforces diversity: at most MAX_PER_PAIR cases per (alpha, beta) pair.

Output: tests/set_theorem_balanced_test.csv
Columns: o_n, o_d, a_n, a_d, period_multiset, period_set
"""

import csv
import os
import sys
from fractions import Fraction
from math import gcd, ceil

# ─── load lambda_period from test_lambda.py ───────────────────────────────────
_here = os.path.dirname(os.path.abspath(__file__))
_c_dir = os.path.join(_here, '..', 'c', 'multiset')
sys.path.insert(0, _c_dir)
from test_lambda import lambda_period  # sort_mode=True → multiset period


# ─── set-period computation ───────────────────────────────────────────────────

def _find_period(gaps, index_start, index_end):
    n = index_end - index_start + 1
    if n < 2:
        return None
    for period in range(1, n // 2 + 1):
        if all(gaps[index_start + i] == gaps[index_start + i + period]
               for i in range(n - period)):
            return period
    return None


def lambda_set_period(alpha, beta, gamma, delta, x_min=0, x_max=5000,
                      fraction_remaining=0.9):
    """
    Set-valued period: collect projected values p̃ = β·x + α·y,
    deduplicate, sort, compute gaps, find minimal period.

    Uses the same adaptive-trim / shrinking-window strategy as lambda_period
    to handle boundary artefacts at x_min and x_max.
    """
    g = gcd(alpha, beta); alpha, beta = alpha // g, beta // g
    g = gcd(gamma, delta); gamma, delta = gamma // g, delta // g

    l = Fraction(alpha * delta * x_min - alpha * gamma, beta * delta)
    u = Fraction(alpha * delta * x_min + beta * gamma, beta * delta)
    to_add = Fraction(alpha, beta)

    p_set = set()
    beta_x = beta * x_min
    for x in range(x_min, x_max):
        ylo = ceil(l)
        yhi = int(u)
        cur = beta_x + alpha * ylo
        for _ in range(yhi - ylo + 1):
            p_set.add(cur)
            cur += alpha
        beta_x += beta
        l += to_add
        u += to_add

    vals = sorted(p_set)
    if len(vals) < 4:
        return None

    gaps = [vals[i + 1] - vals[i] for i in range(len(vals) - 1)]
    n = len(gaps)

    # Adaptive trim: mirrors the sort-mode trim in lambda_period
    to_delete = max(2, int((1.0 - fraction_remaining) / 40.0 * n))

    index_start = to_delete
    index_end = n - 1 - to_delete
    initial_length = index_end - index_start + 1
    current_length = initial_length
    period = None

    while period is None:
        index_start += 1
        index_end -= 1
        current_length -= 2
        if index_start >= index_end:
            break
        if current_length / initial_length < fraction_remaining:
            break
        period = _find_period(gaps, index_start, index_end)

    return period


# ─── case generation ──────────────────────────────────────────────────────────

MAX_PER_PAIR = 5   # max cases per (alpha, beta) — enforces diversity

def collect_cases(target=120):
    """
    Return (cases_lt, cases_ge) each a list of (gamma, delta, alpha, beta, N, D).
    Diverse: at most MAX_PER_PAIR rows per (alpha, beta) pair in each class.
    """
    cases_lt = []
    cases_ge = []
    pair_count_lt = {}
    pair_count_ge = {}

    ALPHA_MAX = 10
    P_MAX = 300
    Q_MAX = 20

    for alpha in range(1, ALPHA_MAX + 1):
        for beta in range(1, ALPHA_MAX + 1):
            if gcd(alpha, beta) != 1:
                continue
            D = alpha * alpha + beta * beta
            pair = (alpha, beta)
            cnt_lt = pair_count_lt.get(pair, 0)
            cnt_ge = pair_count_ge.get(pair, 0)

            for q in range(1, Q_MAX + 1):
                for p in range(1, P_MAX + 1):
                    if gcd(p, q) != 1:
                        continue
                    N = (p * alpha) // q + (p * beta) // q + 1
                    if N < D and cnt_lt < MAX_PER_PAIR and len(cases_lt) < target:
                        # require N >= 2 so the period is non-trivial
                        if N >= 2:
                            cases_lt.append((p, q, alpha, beta, N, D))
                            cnt_lt += 1
                            pair_count_lt[pair] = cnt_lt
                    elif N >= D and cnt_ge < MAX_PER_PAIR and len(cases_ge) < target:
                        cases_ge.append((p, q, alpha, beta, N, D))
                        cnt_ge += 1
                        pair_count_ge[pair] = cnt_ge

                if cnt_lt >= MAX_PER_PAIR and cnt_ge >= MAX_PER_PAIR:
                    break

        if len(cases_lt) >= target and len(cases_ge) >= target:
            break

    return cases_lt, cases_ge


# ─── main ─────────────────────────────────────────────────────────────────────

def main():
    out_path = os.path.normpath(
        os.path.join(_here, '..', '..', 'tests', 'set_theorem_balanced_test.csv'))

    print("Collecting candidate cases …")
    cases_lt, cases_ge = collect_cases(target=120)
    print(f"  N < D: {len(cases_lt)} candidates  (diverse: "
          f"{len(set((c[2],c[3]) for c in cases_lt))} distinct (α,β) pairs)")
    print(f"  N >= D: {len(cases_ge)} candidates  (diverse: "
          f"{len(set((c[2],c[3]) for c in cases_ge))} distinct (α,β) pairs)")

    all_cases = [(c, 'lt') for c in cases_lt] + [(c, 'ge') for c in cases_ge]
    total = len(all_cases)

    rows = []
    skipped = 0

    for idx, ((gamma, delta, alpha, beta, N, D), cls) in enumerate(all_cases, 1):
        print(f"\r  [{idx}/{total}] a={alpha},b={beta},w={gamma}/{delta} "
              f"N={N},D={D} ({cls})    ", end='', flush=True)

        x_max_set = 300 if N >= D else max(3000, 80 * N)
        x_max_multi = x_max_set

        p_set = lambda_set_period(alpha, beta, gamma, delta, x_max=x_max_set)
        if p_set is None:
            skipped += 1
            continue

        p_multi, _ = lambda_period(alpha, beta, gamma, delta,
                                   x_max=x_max_multi, sort_mode=True)
        if p_multi is None:
            skipped += 1
            continue

        rows.append({
            'o_n': gamma, 'o_d': delta,
            'a_n': alpha, 'a_d': beta,
            'period_multiset': p_multi,
            'period_set': p_set,
            'N': N, 'D': D,
        })

    print(f"\n\nComputed {len(rows)} rows, {skipped} skipped.")

    # ── theorem verification ──
    errors_multi = 0
    errors_set = 0
    for r in rows:
        N, D = r['N'], r['D']
        exp_multi = N if N % D != 0 else N // D
        exp_set = N if N < D else 1
        if r['period_multiset'] != exp_multi:
            errors_multi += 1
            print(f"  MISMATCH multiset: {r}, expected {exp_multi}")
        if r['period_set'] != exp_set:
            errors_set += 1
            print(f"  MISMATCH set:      {r}, expected {exp_set}")

    lt_count = sum(1 for r in rows if r['N'] < r['D'])
    ge_count = sum(1 for r in rows if r['N'] >= r['D'])
    print(f"N<D rows: {lt_count}   N>=D rows: {ge_count}")
    print(f"Theorem check: multiset errors={errors_multi}, set errors={errors_set}")

    if errors_multi == 0 and errors_set == 0:
        print("All rows match both theorems.")

    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, 'w', newline='') as f:
        writer = csv.DictWriter(
            f, fieldnames=['o_n', 'o_d', 'a_n', 'a_d', 'period_multiset', 'period_set'])
        writer.writeheader()
        for r in rows:
            writer.writerow({k: r[k] for k in writer.fieldnames})

    print(f"Written: {out_path}")


if __name__ == '__main__':
    main()
