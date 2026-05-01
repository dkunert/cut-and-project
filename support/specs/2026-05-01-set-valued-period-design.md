# Set-Valued Period Formula — Design Document

**Date:** 2026-05-01
**Author:** Dirk Kunert (with Claude as drafting assistant)
**Status:** Draft, awaiting approval before implementation

---

## 1. Goal

Extend the paper currently titled *A Period Formula for Rational Cut-and-Project
Strip Projections with Multiplicity* to cover the **set-valued** gap sequence
(multiplicities discarded), thereby resolving Open Problem 2 of the existing
manuscript and giving a complete picture of $\lambda_{\text{set}}$.

Deliverables:

1. New LaTeX file `LaTeX/rational_cut_and_project_gap_periods.tex` with revised
   title *Period Formulas for Rational Cut-and-Project Strip Projections:
   Multiset and Set Cases* and a new theorem section.
2. Lean 4 verification appended to
   `Lean/CutAndProject/CutAndProject/Basic.lean`.
3. Revision of `LaTeX/set_analysis_results.tex` to align with the new theorem.

Out of scope:

- Higher-dimensional cases (Open Problem 3 remains open).
- Window-position dependence (Open Problem 1 remains open).
- Distribution of gap lengths (Open Problem 4 remains open).
- Redesign of the C `add_period_set` heuristic.

---

## 2. The result

### Theorem (Set-Valued Period)

Let $\alpha, \beta \in \mathbb{N}$ be coprime, $\omega \ge 0$,
$N = \lfloor\omega\alpha\rfloor + \lfloor\omega\beta\rfloor + 1$, and
$D = \alpha^2 + \beta^2$. The set-valued gap sequence has minimal period

$$
\lambda_{\text{set}} \;=\; \begin{cases} N & \text{if } N < D, \\ 1 & \text{if } N \ge D. \end{cases}
$$

### Corollary

$\lambda_{\text{set}} \le \lambda_{\text{multiset}}$ in every case, with
equality if and only if $N \le D$.

### Proof sketch (two cases)

Write $q = \lfloor N/D\rfloor$. By Lemma 4.3 (non-uniform residue distribution)
and its uniform companion (currently inlined in the proof of Theorem 5.1, to be
extracted), the multiplicity function $\mu \colon \mathbb{Z}/D\mathbb{Z} \to
\mathbb{N}_0$ takes values in $\{q, q+1\}$.

**Case $N < D$.** Then $q = 0$, so $\mu \in \{0, 1\}$. By §4 Step 5's
structural decomposition, integer $z$ has multiplicity $\mu(z \bmod D) \le 1$
in the bi-infinite multiset; the multiset has no duplicates, so multiset = set
as $\mathbb{Z}$-indexed sequences. Since $0 < N < D$ implies $D \nmid N$,
Theorem 3.1 gives $\lambda_{\text{multiset}} = N$. Hence $\lambda_{\text{set}}
= N$.

**Case $N \ge D$.** Then $q \ge 1$, so $\mu \ge 1$ everywhere. Every residue
class is hit, so the underlying set is
$\bigcup_{r \in \mathbb{Z}/D}(r + D\mathbb{Z}) = \mathbb{Z}$. The gap sequence
of $\mathbb{Z}$ is constant $1$, with minimal period $1$.

---

## 3. Open-item checks (resolved)

### Uniform companion to Lemma 4.3 — **INLINED**

The statement "$D \mid N \Rightarrow \mu \equiv N/D$" is currently embedded in
the proof of Theorem 5.1 (lines 568–576 of the existing paper):

> "When $D \mid N$, the $N$ values of $r$ span exactly $N/D$ complete cycles
> of the map $r \mapsto mr \bmod D$. […] each residue class $c$ is hit
> exactly $N/D$ times."

**Action:** the new theorem's proof should make this explicit as a one-line
auxiliary statement (or a named Lemma adjacent to Lemma 4.3) so that both the
multiset and set theorems can cite it cleanly.

### Bi-infinite indexing convention — **CONFIRMED**

`subsec:distance` (line 213) states:

> "the resulting multiset is locally finite and unbounded in both directions.
> It therefore admits a nondecreasing enumeration indexed by $\mathbb{Z}$
> […] $(\tilde{p}^{(i)}_s)_{i \in \mathbb{Z}}$"

and Definition 2.1 (line 229) defines minimal period as the smallest positive
integer $\lambda$ with $\delta^{(i+\lambda)} = \delta^{(i)}$ for all
$i \in \mathbb{Z}$. The new theorem's set-valued proof inherits this
convention without modification.

---

## 4. Empirical verification record

Eight worked examples, all consistent with the dichotomy:

| # | $\alpha$ | $\beta$ | $\omega$ | $D$ | $N$ | regime | $\lambda_{\text{multiset}}$ | $\lambda_{\text{set}}$ predicted | C tool output |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 1 | 2 | 0.5 | 5 | 2 | $N<D$, $D\nmid N$ | 2 | 2 | 2 ✓ |
| 2 | 1 | 2 | 1.5 | 5 | 5 | $D\mid N$, $N=D$ | 1 | 1 | 1 ✓ |
| 3 | 1 | 2 | 2.5 | 5 | 8 | $N>D$, $D\nmid N$ | 8 | 1 | 1 ✓ |
| 4 | 2 | 3 | 0.5 | 13 | 3 | $N<D$, $D\nmid N$ | 3 | 3 | 3 ✓ |
| 5 | 2 | 3 | 2.0 | 13 | 11 | $N<D$, $D\nmid N$ | 11 | 11 | 11 ✓ |
| 6 | 2 | 3 | 3.0 | 13 | 16 | $N>D$, $D\nmid N$ | 16 | 1 | 1 ✓ |
| 7 | 3 | 4 | 4.0 | 25 | 29 | $N>D$, $D\nmid N$ | 29 | 1 | 1 ✓ |

Inputs/outputs:
- `tests/six_examples_input.csv`, `tests/six_examples_output.csv`
- `tests/seventh_example_input.csv`, `tests/seventh_example_output.csv`

The decisive rows are #3, #6, #7 (all with $N > D$ and $D \nmid N$): the
hypothesis "$D \nmid N \Rightarrow \lambda_{\text{set}} = N$" predicts $N$;
the actual value is 1, matching the new dichotomy.

---

## 5. Paper revision plan

All edits in `LaTeX/rational_cut_and_project_gap_periods.tex` (the new file).
Original `rational_cut_and_project_multiset_gap_periods.tex` is preserved
unchanged.

### 5.1 Title

Already done: `Period Formulas for Rational Cut-and-Project Strip Projections:
Multiset and Set Cases`.

### 5.2 Abstract

Update to mention both formulas. Current abstract describes only the multiset
case.

### 5.3 §2.4 Multiplicity convention (line 193)

Update so that *both* conventions (multiset and set) are introduced
symmetrically, with a forward reference to §6.

### 5.4 New auxiliary lemma (in §4)

Extract the inlined "uniform residue distribution" statement from the proof of
Theorem 5.1 into a named **Lemma 4.4 (Uniform residue distribution)**:

> If $D \mid N$, then $\mu(c) = N/D$ for every $c \in \mathbb{Z}/D\mathbb{Z}$.

Place adjacent to Lemma 4.3. The proof of Theorem 5.1 then cites Lemma 4.4
instead of inlining; the new §6 theorem also cites Lemma 4.4.

### 5.5 New §6 "Set-Valued Period"

Insert a new section **between §5 (Degenerate case) and §6 (Corollaries)**.
Renumbers existing §6 → §7, §7 → §8, etc. Table 1 in `subsec:lean_corr`
references Lean line numbers, not paper section numbers — no impact.

Contents:

- Definition of set-valued gap sequence (~4 lines).
- Theorem 6.1 (Set-valued period) — statement.
- Proof — two cases as in §2 above (~12 lines).
- Corollary 6.2 — $\lambda_{\text{set}} \le \lambda_{\text{multiset}}$, equality iff $N \le D$.
- Examples revisited: Examples 5.1, 5.2, plus a new Example covering $N > D, D \nmid N$.
- Forward reference to `set_analysis_results.tex` for empirical data.

### 5.6 §5 Remark at line 617

Update the existing remark "The boundary case $N=D$ […] gives $\lambda=1$" to
point at the new §6 theorem, or move it into §6.

### 5.7 §9.2 (subsec:discarding) — DELETE

Content is fully superseded by the new §6. Remove the subsection. The
`\section{Discussion}` then has only §9.1 (case split) and §9.2 (Open
problems, renumbered down).

### 5.8 §9.3 → §9.2 Open problems

Remove item 2 (set-valued gap sequence). Renumber items 3, 4 → 2, 3.

### 5.9 Lean correspondence (Table 1 in `subsec:lean_corr`)

Add new rows for the new Lean declarations (names + line numbers). Filled in
*after* the Lean port (Phase 7).

---

## 6. `set_analysis_results.tex` revision plan

### 6.1 Section "Why $\lambda_{\text{set}} = 1$ is reported for this row"

Currently attributes the disagreement row $(α=68, β=149, ω≈707)$ to an
algorithmic artifact. **Replace** with a structural explanation citing the new
Theorem 6.1: $D = 26{,}825$, $N = 153{,}431$, so $N \gg D$ and the theorem
predicts $\lambda_{\text{set}} = 1$. The reported value is the correct
mathematical answer.

### 6.2 "Aggregate counts" / "Updated picture" sections

Add interpretive note: the 99.97% agreement rate reflects that the input CSV
is concentrated in the $N < D$ regime where $\lambda_{\text{set}} =
\lambda_{\text{multiset}}$.

### 6.3 New section "Distribution by regime" (optional)

Compute, from `tests/new_find_patterns_x_max_1000000_51012_lines.csv`, the
breakdown of input rows by $N < D$ vs $N \ge D$. Expected: the $N < D$ count
is ~50,968 and the $N \ge D$ count is ~43 (matching the ~99.92% agreement
plus the ~43 abort rows). Decide before implementation whether this is worth
the ~30-line script.

### 6.4 Post-mortem on the 17 remaining `-4` (timeout) rows

One sentence: under Theorem 6.1, all $N \ge D$ rows have
$\lambda_{\text{set}} = 1$ in $O(1)$ time. The C heuristic would benefit from
this short-circuit but redesigning it is out of scope.

---

## 7. Lean port plan

### 7.1 Strategy

Append-only edit to `Basic.lean` *after* the current end (line 1313). Existing
Table 1 line numbers (lines 11, 20, 43, 140, 215, 269, 334, 388, 1206, 1233,
1283) are preserved. New declarations get line numbers $\ge 1314$.

### 7.2 New declarations (sketch)

```lean
-- Two structural lemmas linking N vs D to count_hits range.
lemma count_hits_le_one_of_lt_D (h : N < D) : ∀ r, count_hits ... r ≤ 1
lemma count_hits_ge_one_of_ge_D (h : N ≥ D) : ∀ r, count_hits ... r ≥ 1

-- Set-valued analogue of difference_sequence.
def set_difference_sequence (α β : ℕ) (ω : ℝ) : ℤ → ℤ := ...

-- Two case lemmas.
lemma set_period_lt_D (h : N < D) : HasPeriodLength set_difference_sequence N
lemma set_period_ge_D (h : N ≥ D) : HasPeriodLength set_difference_sequence 1

-- Final theorem.
theorem set_main_theorem (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ)
    (h_ω : 0 ≤ ω) [NeZero (α^2 + β^2)] :
    HasPeriodLength (set_difference_sequence α β ω)
      (if N < D then N else 1)
```

Estimated 150–300 new lines.

### 7.3 Hard parts

- Defining `set_difference_sequence` rigorously. Cleanest is probably via the
  enumeration of $\{z : \mu(z \bmod D) \ge 1\}$ in $\mathbb{Z}$, lifted via
  `Nat.find` or similar. This bookkeeping does not appear in the paper proof.
- The "$\mu \le 1 \Rightarrow$ multiset = set" step requires showing two
  $\mathbb{Z} \to \mathbb{Z}$ functions are equal. Mechanical but tedious.
- May require extending or paralleling the existing `GeometricProjection`
  typeclass. If extension is too multiset-specific, fallback is a parallel
  `SetGeometricProjection` typeclass.

### 7.4 Gate

**Paper revision (Phase 5) does not start until Lean port closes with no
`sorry`.** If Lean surfaces a bookkeeping issue, fix here before any paper
edit. This catches any subtle gap in the proof structure before publication.

---

## 8. Workflow

1. ✅ Empirical verification (7 worked examples + C tool).
2. ✅ Open-item checks (uniform companion inlined; bi-infinite confirmed).
3. ✅ New LaTeX file created with new title.
4. ✅ Design document written (this file).
5. **User reviews this design document.**
6. **Lean port** in `Basic.lean` (Phase 7 above). Gate: no `sorry`.
7. **Paper revision** in `rational_cut_and_project_gap_periods.tex` (Phase 5
   above), with Table 1 updated to include new Lean references.
8. **`set_analysis_results.tex` revision** (Phase 6 above).
9. Final review pass: build paper, ensure all cross-references resolve,
   ensure Lean still builds.

---

## 9. Risks and open questions

- **Lean port complexity:** the 150–300-line estimate is rough. If
  `set_difference_sequence` definition turns out to be substantially harder
  than expected (e.g., if the enumeration construction requires Mathlib
  machinery that isn't readily available), the gate may stall. Mitigation: at
  the first sign of trouble, pause and brainstorm a leaner formulation
  (e.g., prove the dichotomy in terms of `count_hits` only, deferring the
  set-difference-sequence enumeration to a separate lemma).
- **`add_period_set` heuristic:** out of scope, but if the new theorem
  invalidates assumptions in the heuristic (it doesn't — the heuristic just
  becomes redundant for $N \ge D$), a follow-up should be considered.
- **Dateiname / external references:** if the original paper has been
  uploaded to arXiv or referenced externally, renaming the file (and shifting
  the citation) may need coordination. Mitigation: keep both files until
  publication is settled; only delete the multiset-only file once the
  combined paper is final.

---

## 10. Approval gate

This design is awaiting user review. Once approved, proceed to Phase 6 (Lean
port). Do not begin Phase 7 (paper revision) until Phase 6 closes cleanly.
