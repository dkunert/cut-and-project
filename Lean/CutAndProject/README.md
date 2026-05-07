# CutAndProject — Lean 4 Formalisation

This directory contains a Lean 4 formalisation of the residue-combinatorial core of both period-length theorems for one-dimensional rational cut-and-project gap sequences (multiset and set conventions), as proved in `../../LaTeX/rational_cut_and_project_gap_periods.tex`.

The formalisation is approximately 2,860 lines of verified code in `CutAndProject/Basic.lean` and contains no `sorry`, `admit`, or `axiom`.

## Scope

The proof is structured in two layers.

The first layer states an abstract typeclass `GeometricProjection` collecting four axioms (positivity of `N`, that `N` is a period of the difference sequence, the degenerate case `D ∣ N`, and that any period induces a residue-preserving translation). Given these axioms, the generic minimality argument (`generic_minimality`) and the case dispatch (`main_theorem`) are proved purely algebraically.

The second layer constructs a concrete instance (`GeometricProjectionConcrete`) by defining the sorted multiset and the difference sequence explicitly, then discharges each axiom by a separate lemma:

* `N_pos_concrete`
* `period_N_concrete`
* `period_degenerate_concrete`
* `sigma_of_period_concrete`

The set-valued companion theorem mirrors this construction with the multiplicity function flattened to `{0, 1}`: `set_V` replaces `V`, `set_size` replaces `N`, and `set_main_theorem` / `set_main_theorem_concrete` discharge the dichotomy `N < D` versus `N ≥ D`. The unit-aware variants (`main_theorem_geometric_concrete`, `set_main_theorem_geometric_concrete`) thread the geometric multiplier `c_r ≡ -α β⁻¹ r (mod D)` through to the headline statements.

The geometric reduction from the strip construction to the residue multiset is represented at the combinatorial level: the sorted multiset is defined as

```
p_s(i) := V(i mod N) + (i / N) * D
```

where `V` is the quantile function of the cumulative residue distribution. The bridge lemma `count_hits_eq_sorted_count` verifies this is consistent with the residue counting function.

Thus the formalisation verifies the residue-combinatorial core of both proofs (multiset and set), with the geometric multiplier threaded through to the headline statements; the strip-to-residue reduction itself is hand-verified in Sections 2 and 3.2 of the paper.

## Correspondence with the paper

Table 1 of the paper lists the correspondence between paper results and Lean declarations, including line numbers in `CutAndProject/Basic.lean`.

## Versions

* Lean: `leanprover/lean4:v4.29.1` (pinned in `lean-toolchain`).
* Mathlib: `v4.29.1`, exact commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6` (pinned in `lake-manifest.json`).

## Building

Install [`elan`](https://github.com/leanprover/elan); it will pick up the toolchain pinned in `lean-toolchain` automatically. Then, from this directory:

```
lake exe cache get   # download Mathlib build cache (recommended)
lake build
```

`lake build` should report `Build completed successfully` with no warnings. Three Mathlib style linters (`linter.style.longLine`, `linter.style.maxHeartbeats`, `linter.style.induction`) are silenced in `lakefile.toml`; their fixes would shift line numbers referenced by Table 1 of the companion paper.

## Layout

```
Lean/CutAndProject/
├── CutAndProject.lean           # entry point (imports CutAndProject.Basic)
├── CutAndProject/
│   └── Basic.lean               # the full formalisation
├── lakefile.toml                # build configuration
├── lake-manifest.json           # exact dependency revisions
├── lean-toolchain               # Lean version
└── README.md                    # this file
```
