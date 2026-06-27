# CutAndProject — Lean 4 Formalisation

This directory contains a Lean 4 formalisation of all period theorems for one-dimensional cut-and-project gap sequences proved in `../../LaTeX/rational_cut_and_project_gap_periods.tex`.

The formalisation comprises approximately 3,750 lines of verified code split across two files in `CutAndProject/`, and contains no `sorry`, `admit`, or `axiom`.

* `Basic.lean` (~2,860 lines) — rational case: the residue-combinatorial core for both period theorems (multiset and set conventions).
* `Irrational.lean` (~900 lines) — irrational case: aperiodicity of the projected gap sequence for irrational slope.

## Scope: rational case (`Basic.lean`)

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

Thus `Basic.lean` verifies the residue-combinatorial core of both proofs (multiset and set), with the geometric multiplier threaded through to the headline statements; the strip-to-residue reduction itself is hand-verified in Sections 2 and 3.2 of the paper.

## Scope: irrational case (`Irrational.lean`)

For positive irrational slope `a` and strip half-width `ω > 0`, `Irrational.lean` proves Proposition 1 of the paper (Section "The Irrational Case"): the projected gap sequence has no finite period. The headline theorem is `prop_irrational`; the corollary `tildeP_injOn_acceptedSet` formalises the second clause ("multiset and set conventions coincide" because the projection is injective on `ℤ²`).

Beyond the proposition itself, the file establishes the supporting infrastructure used implicitly in the paper proof: local finiteness of `tildeP(A)`, bi-infinite unboundedness, and the resulting `ℤ`-indexed enumeration of accepted projected points (assembled via Mathlib's `orderIsoIntOfLinearSuccPredArch`). Kronecker density of `ℤ + a·ℤ ⊂ ℝ` is reduced to Mathlib's `dense_addSubgroupClosure_pair_iff`.

## Correspondence with the paper

Table 1 of the paper lists the correspondence between paper results and Lean declarations, with line numbers for both `Basic.lean` (rational case) and `Irrational.lean` (irrational case).

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
├── CutAndProject.lean           # entry point (imports CutAndProject.Basic and CutAndProject.Irrational)
├── CutAndProject/
│   ├── Basic.lean               # rational case (~2,860 lines)
│   └── Irrational.lean          # irrational case (~900 lines)
├── lakefile.toml                # build configuration
├── lake-manifest.json           # exact dependency revisions
├── lean-toolchain               # Lean version
└── README.md                    # this file
```
