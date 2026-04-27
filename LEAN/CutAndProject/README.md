# CutAndProject — Lean 4 Formalisation

This directory contains a Lean 4 formalisation of the algebraic core of the period-length theorem for one-dimensional rational cut-and-project multiset gap sequences, as proved in `../../LaTeX/rational_cut_and_project_multiset_gap_periods.tex`.

The formalisation is approximately 1,300 lines of verified code in `CutAndProject/Basic.lean` and contains no `sorry`, `admit`, or `axiom`.

## Scope

The proof is structured in two layers.

The first layer states an abstract typeclass `GeometricProjection` collecting four axioms (positivity of `N`, that `N` is a period of the difference sequence, the degenerate case `D ∣ N`, and that any period induces a residue-preserving translation). Given these axioms, the generic minimality argument (`generic_minimality`) and the case dispatch (`main_theorem`) are proved purely algebraically.

The second layer constructs a concrete instance (`GeometricProjectionConcrete`) by defining the sorted multiset and the difference sequence explicitly, then discharges each axiom by a separate lemma:

* `N_pos_concrete`
* `period_N_concrete`
* `period_degenerate_concrete`
* `sigma_of_period_concrete`

The geometric reduction from the strip construction to the residue multiset is represented at the combinatorial level: the sorted multiset is defined as

```
p_s(i) := V(i mod N) + (i / N) * D
```

where `V` is the quantile function of the cumulative residue distribution. The bridge lemma `count_hits_eq_sorted_count` verifies this is consistent with the residue counting function.

Thus the formalisation verifies the algebraic core of the proof, not the full analytic geometry from first principles.

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

`lake build` should report `Build completed successfully`. Some Mathlib style linter warnings (long lines, deprecated tactics) remain; none affect correctness.

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
