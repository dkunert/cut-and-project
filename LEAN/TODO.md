# LEAN Formalization: Remaining Tasks

## Current State

The algebraic/combinatorial core of the proof is fully machine-checked:
- Coprimality lemmas (Lemma 4.1)
- Residue bijection and multiplier
- Non-uniform and uniform residue distribution (Lemma 4.3)
- Heavy set is a contiguous cyclic interval
- Trivial stabiliser of cyclic intervals (minimality)
- Generic minimality argument (Step 5)
- Main theorem structure (dispatches to degenerate/generic cases)

The proof relies on a `GeometricProjection` typeclass (4 axioms) that
abstracts the interface between the geometric construction and the algebraic
proof. What remains is to construct a concrete instance of this typeclass.

---

## Task 1: Define `difference_sequence` concretely

**Status:** Currently `opaque` (Basic.lean, line 439)

**What to do:**
1. For each integer $r \in \mathcal{R} = \{-\lfloor\beta\omega\rfloor, \ldots, \lfloor\alpha\omega\rfloor\}$, define the residue $c_r \equiv -\alpha\beta^{-1}r \pmod{D}$.
2. Define the arithmetic progression $P_r = \{c_r + kD : k \in \mathbb{Z}\}$.
3. Form the multiset $S = \bigcup_{r \in \mathcal{R}} P_r$.
4. Define a sorting/ordering on $S$ and extract consecutive differences.

**Difficulty:** Hard. Formalizing the sorting of an infinite periodic multiset
indexed by $\mathbb{Z}$ in Lean 4 / Mathlib is non-trivial. One approach is
to work within a single period $[0, D)$ and define the difference sequence
combinatorially from the sorted residues, then extend periodically.

---

## Task 2: Prove `N_pos` — $N > 0$

**Status:** Not yet proven

**What to do:** Show $N = \lfloor\omega\alpha\rfloor + \lfloor\omega\beta\rfloor + 1 \geq 1$.

**Difficulty:** Easy. The $+1$ makes this immediate.

---

## Task 3: Prove `period_N` — the sequence has period $N$

**Status:** Not yet proven

**What to do:** Show that within each interval $[kD,\, (k+1)D)$ on the
$\tilde{p}$-axis, exactly $N$ points from $S$ fall (one from each
progression $P_r$). The relative positions within the interval are the
residues $c_r \bmod D$, which are the same in every interval. Therefore
the sorted difference sequence repeats with period $N$.

**Difficulty:** Moderate. Requires the concrete construction from Task 1.

---

## Task 4: Prove `period_degenerate` — when $D \mid N$, minimal period is $N/D$

**Status:** Not yet proven

**What to do:**
1. When $D \mid N$, every residue class is hit exactly $N/D$ times
   (already proven: `uniform_residue_distribution`).
2. Conclude that every integer is a $\tilde{p}$-value with multiplicity $N/D$.
3. The difference sequence becomes $(0, \ldots, 0, 1, 0, \ldots, 0, 1, \ldots)$
   with block length $N/D$.
4. Show this pattern has minimal period $N/D$.

**Difficulty:** Easy to moderate. Step 1 is done; steps 2-4 follow from the
explicit form of the sequence.

---

## Task 5: Prove `sigma_of_period` — sub-periods induce residue-preserving translations

**Status:** Not yet proven

**What to do:** Given a period $L$ of the difference sequence:
1. The sum of $L$ consecutive gaps equals some value $\sigma$.
2. Show $\sigma \cdot N = L \cdot D$ (because $N$ gaps always sum to $D$).
3. Translation by $\sigma$ on the $\tilde{p}$-axis maps $S$ to itself.
4. Conclude that the residue multiplicity function $\mu$ satisfies
   $\mu(c + \sigma) = \mu(c)$ for all $c \in \mathbb{Z}/D\mathbb{Z}$.

**Difficulty:** Moderate. Requires the concrete construction from Task 1
and properties of the sorted multiset.

---

## Summary

| Task | Description                        | Difficulty | Depends on |
|------|------------------------------------|------------|------------|
| 1    | Define `difference_sequence`       | Hard       | —          |
| 2    | Prove `N_pos`                      | Easy       | Task 1     |
| 3    | Prove `period_N`                   | Moderate   | Task 1     |
| 4    | Prove `period_degenerate`          | Easy-Mod.  | Task 1     |
| 5    | Prove `sigma_of_period`            | Moderate   | Task 1     |

Task 1 is the bottleneck. All other tasks depend on it. One strategy to
reduce complexity: define the difference sequence combinatorially from the
sorted residues within one period $[0, D)$, avoiding the need to formalize
infinite sorted multisets directly.
