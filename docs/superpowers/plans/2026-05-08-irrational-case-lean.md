# Irrational Case in Lean 4 — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize Proposition 1 of `LaTeX/rational_cut_and_project_gap_periods.tex` Section "The Irrational Case" (lines 1259–1339) in Lean 4: for irrational slope `a > 0` and `ω > 0`, the projected gap sequence has no finite period.

**Architecture:** Add a new self-contained file `Lean/CutAndProject/CutAndProject/Irrational.lean` (~500 lines). `Basic.lean` is **not modified** (paper Table 1 pins its line numbers). The new file uses different machinery than `Basic.lean` (real-valued topology + irrationality, not modular arithmetic), so it is logically and physically separate. Connect it to the build via the root `CutAndProject.lean` aggregator.

**Tech Stack:** Lean 4 + Mathlib `v4.29.1` (already pinned in `lakefile.toml`). Key Mathlib pieces:
- `Mathlib.Topology.Algebra.Order.Archimedean` — `AddSubgroup.dense_or_cyclic`
- `Mathlib.Order.SuccPred.LinearLocallyFinite` — `orderIsoIntOfLinearSuccPredArch`, `LinearLocallyFiniteOrder.succOrder`/`predOrder`
- `Mathlib.Order.Interval.Finset.Defs` — `LocallyFiniteOrder.ofFiniteIcc`
- `Mathlib.Data.Real.Irrational` — `Irrational` predicate

`Basic.lean` already does `import Mathlib`, so no granular import management needed in the new file either.

**Style constraints:**
- 0 `sorry`, 0 warnings, 0 errors at the end of every task. (Within a task, a temporary `sorry` is allowed only between Step 1 and Step 3.)
- File header doc-string in the same style as `Basic.lean`.
- One `theorem` / `lemma` / `def` per public name; helper proofs may be `private`.
- Names follow Mathlib convention (`snake_case` for theorems, `camelCase` for definitions).

---

## File Structure

**Create:**
- `Lean/CutAndProject/CutAndProject/Irrational.lean` — entire new module

**Modify:**
- `Lean/CutAndProject/CutAndProject.lean` — add one import line (currently 1 line: `import CutAndProject.Basic`)

**Do not modify:**
- `Lean/CutAndProject/CutAndProject/Basic.lean` — paper Table 1 pins line numbers
- `Lean/CutAndProject/lakefile.toml` — `import Mathlib` already provides everything

**Logical layout inside `Irrational.lean`:**
```
Section A — Notation and accepted set         (~ 60 lines)
Section B — Step 1: tildeP injectivity        (~ 25 lines)
Section C — Kronecker density bridge          (~ 40 lines)
Section D — Local finiteness of tildeP '' A   (~ 90 lines)
Section E — Bi-infinite unboundedness          (~ 80 lines)
Section F — ℤ-enumeration via orderIso         (~ 40 lines)
Section G — Gap sequence + periodicity         (~ 50 lines)
Section H — Step 2: period → lattice transl.   (~ 110 lines)
Section I — Step 3: density forces v = 0       (~ 80 lines)
Section J — Main theorem prop_irrational       (~ 40 lines)
```

---

## Task 1: Skeleton file + build registration

**Files:**
- Create: `Lean/CutAndProject/CutAndProject/Irrational.lean`
- Modify: `Lean/CutAndProject/CutAndProject.lean`

- [ ] **Step 1: Create skeleton with module doc-string**

```lean
/-
Aperiodicity of the projected gap sequence for irrational slopes.

This file formalizes Proposition 1 of
`LaTeX/rational_cut_and_project_gap_periods.tex`, Section
"The Irrational Case" (lines 1259–1339). For positive irrational
slope `a` and strip half-width `ω > 0`, the projected gap sequence
on the accepted lattice points has no finite period.

The proof has three steps:
  1. The physical projection `p̃(x,y) = x + a*y` is injective on `ℤ²`.
  2. A finite period of the gap sequence lifts to a non-zero
     translation `v ∈ ℤ²` that preserves the accepted set `A`.
  3. Such a translation must induce a non-zero internal shift `τ`
     that preserves `W ∩ s(ℤ²)`; Kronecker density on `ℝ` rules
     this out, forcing `v = 0` and contradicting Step 2.
-/
import Mathlib

open Set Function

namespace CutAndProject.Irrational

end CutAndProject.Irrational
```

- [ ] **Step 2: Register module in root**

Modify `Lean/CutAndProject/CutAndProject.lean` from
```lean
import CutAndProject.Basic
```
to
```lean
import CutAndProject.Basic
import CutAndProject.Irrational
```

- [ ] **Step 3: Build, verify 0 errors / 0 warnings**

Run: `cd Lean/CutAndProject && lake build`
Expected: build succeeds, no warnings.

- [ ] **Step 4: Commit**

```bash
git add Lean/CutAndProject/CutAndProject.lean \
        Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: add Irrational.lean skeleton (no content yet)"
```

---

## Task 2: Notation and accepted set (Section A)

**Files:**
- Modify: `Lean/CutAndProject/CutAndProject/Irrational.lean`

The paper uses `a : ℝ` for the slope, `ω : ℝ` for the half-width, `tildeP(x,y) = x + a*y`, `s(x,y) = y - a*x`, `W = [-a*ω, ω]`, `A = {(x,y) ∈ ℤ² : s(x,y) ∈ W}`.

- [ ] **Step 1: Add the section block with definitions**

Insert inside the namespace (between `namespace` and `end`):

```lean
/-! ### Section A. Notation and accepted set -/

variable (a ω : ℝ)

/-- Physical (signed-position) projection used in the irrational
case: `p̃(x,y) = x + a*y`. -/
def tildeP : ℤ × ℤ → ℝ := fun z => (z.1 : ℝ) + a * (z.2 : ℝ)

/-- Internal coordinate: `s(x,y) = y - a*x`. -/
def sInternal : ℤ × ℤ → ℝ := fun z => (z.2 : ℝ) - a * (z.1 : ℝ)

/-- Internal window `W = [-a*ω, ω]`. -/
def W : Set ℝ := Set.Icc (-(a * ω)) ω

/-- Accepted lattice points: those whose internal coordinate lies in `W`. -/
def acceptedSet : Set (ℤ × ℤ) := {z | sInternal a z ∈ W a ω}
```

- [ ] **Step 2: Build, verify 0 errors / 0 warnings**

Run: `cd Lean/CutAndProject && lake build`

- [ ] **Step 3: Commit**

```bash
git add Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: add notation and accepted set for irrational case"
```

---

## Task 3: Step 1 — `tildeP` injective on `ℤ²` (Section B)

**Files:**
- Modify: `Lean/CutAndProject/CutAndProject/Irrational.lean`

Paper proof (lines 1289–1295): if `tildeP(z₁) = tildeP(z₂)` then
`(x₁-x₂) = -a*(y₁-y₂)`. If `y₁ ≠ y₂`, dividing gives `a ∈ ℚ`,
contradiction. Hence `y₁ = y₂` and then `x₁ = x₂`.

- [ ] **Step 1: Add theorem with `sorry`**

Insert after Section A:

```lean
/-! ### Section B. Step 1: `tildeP` is injective on `ℤ²` -/

theorem tildeP_injective (ha : Irrational a) :
    Function.Injective (tildeP a) := by
  sorry
```

- [ ] **Step 2: Build with sorry, verify type-correct**

Run: `cd Lean/CutAndProject && lake build`
Expected: `declaration uses 'sorry'` warning only.

- [ ] **Step 3: Replace `sorry` with full proof**

```lean
theorem tildeP_injective (ha : Irrational a) :
    Function.Injective (tildeP a) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  -- h : (x₁ : ℝ) + a*y₁ = (x₂ : ℝ) + a*y₂
  -- Rearrange: (x₁ - x₂ : ℝ) = a * (y₂ - y₁ : ℝ).
  by_cases hy : y₁ = y₂
  · -- y₁ = y₂ forces x₁ = x₂ via cancellation
    subst hy
    have hx : (x₁ : ℝ) = (x₂ : ℝ) := by
      have : (x₁ : ℝ) + a*(y₁:ℝ) = (x₂ : ℝ) + a*(y₁:ℝ) := by
        simpa [tildeP] using h
      linarith
    exact Prod.mk.injEq .. |>.mpr ⟨by exact_mod_cast hx, rfl⟩
  · -- y₁ ≠ y₂ forces a ∈ ℚ, contradiction.
    exfalso
    have hxy : ((x₁ - x₂ : ℤ) : ℝ) = a * ((y₂ - y₁ : ℤ) : ℝ) := by
      push_cast
      have := h; simp [tildeP] at this; linarith
    have hne : ((y₂ - y₁ : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (Ne.symm hy)
    have : a = ((x₁ - x₂ : ℤ) : ℝ) / ((y₂ - y₁ : ℤ) : ℝ) := by
      field_simp at hxy ⊢; linarith
    -- a is then rational, contradicting `Irrational a`
    exact ha ⟨(x₁ - x₂) / (y₂ - y₁), by
      rw [this]; push_cast; ring⟩
```

*(The exact tactic invocations may need 2–3 trial-and-error iterations;
the math is straightforward, the Lean is mechanical.)*

- [ ] **Step 4: Build, verify 0 sorry / 0 warnings**

Run: `cd Lean/CutAndProject && lake build`
Expected: clean build.

- [ ] **Step 5: Commit**

```bash
git add Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: Step 1 — tildeP injective on ℤ² (irrational case)"
```

---

## Task 4: Kronecker density bridge (Section C)

**Files:**
- Modify: `Lean/CutAndProject/CutAndProject/Irrational.lean`

Goal: prove that the additive subgroup `ℤ + a·ℤ ⊂ ℝ` is dense for
irrational `a`. Mathlib's `AddSubgroup.dense_or_cyclic` does the heavy
lifting; the cyclic branch gives `1 = m·c` and `a = n·c`, hence
`a = n/m ∈ ℚ`, contradicting `Irrational a`.

- [ ] **Step 1: Add theorem with `sorry`**

```lean
/-! ### Section C. Kronecker density of `ℤ + a·ℤ` -/

/-- For irrational `a`, the set `{n - a*m : m, n ∈ ℤ}` is dense in `ℝ`. -/
theorem dense_internal_image (ha : Irrational a) :
    Dense (Set.range (sInternal a)) := by
  sorry
```

- [ ] **Step 2: Build, verify type-correct (sorry warning only)**

- [ ] **Step 3: Replace `sorry`**

Strategy: build the additive subgroup `S := AddSubgroup.closure {1, a}`
of `ℝ`. Apply `AddSubgroup.dense_or_cyclic`. Cyclic branch: extract
generator `c`, then `1 = m·c`, `a = n·c` with `m, n : ℤ`, so
`a = (n : ℝ) / m ∈ ℚ`. Contradiction with `ha`.

```lean
theorem dense_internal_image (ha : Irrational a) :
    Dense (Set.range (sInternal a)) := by
  -- Reformulate range as AddSubgroup S = closure {1, a}
  set S : AddSubgroup ℝ := AddSubgroup.closure {1, a}
  have hS_range : (S : Set ℝ) = Set.range (sInternal a) := by
    -- Each element n - a*m of S corresponds to (m, n) ∈ ℤ × ℤ.
    -- Forward: closure-induction on {1, a}.
    -- Backward: n - a*m = n*1 + (-m)*a ∈ S.
    sorry  -- ~15 lines of subgroup membership manipulation
  rw [← hS_range]
  rcases AddSubgroup.dense_or_cyclic S with hd | ⟨c, hc⟩
  · exact hd
  · -- Cyclic case: derive a ∈ ℚ
    exfalso
    have h1 : (1 : ℝ) ∈ S := AddSubgroup.subset_closure (by simp)
    have ha_mem : a ∈ S := AddSubgroup.subset_closure (by simp)
    rw [hc] at h1 ha_mem
    rcases AddSubgroup.mem_closure_singleton.mp h1 with ⟨m, hm⟩
    rcases AddSubgroup.mem_closure_singleton.mp ha_mem with ⟨n, hn⟩
    -- 1 = m • c, a = n • c, hence a = (n : ℝ) / m  (with m ≠ 0).
    -- Then `Irrational a` fails.
    sorry  -- ~10 lines: rule out m = 0, divide, use ha
```

*(The two inner `sorry`s are sub-tasks within this task — they should
be eliminated before moving on.)*

- [ ] **Step 4: Build with all sub-sorries resolved, verify clean**

- [ ] **Step 5: Commit**

```bash
git add Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: Kronecker density of ℤ + a·ℤ for irrational a"
```

---

## Task 5: Local finiteness of `tildeP '' acceptedSet` (Section D)

**Files:**
- Modify: `Lean/CutAndProject/CutAndProject/Irrational.lean`

Paper claim (lines 1233–1240): the preimage of any bounded interval,
intersected with the strip, is a bounded parallelogram in `ℝ²` and
hence contains finitely many lattice points.

In Lean: prove that for every `b₁ ≤ b₂`, the set
`{z ∈ acceptedSet | tildeP z ∈ Icc b₁ b₂}` is finite.

- [ ] **Step 1: Add theorem with `sorry`**

```lean
/-! ### Section D. Local finiteness of the projected accepted set -/

/-- The preimage in `ℤ²` of any bounded interval, intersected with the
accepted set, is finite. -/
theorem accepted_preimage_finite
    (ha : Irrational a) (hω : 0 < ω) (b₁ b₂ : ℝ) :
    Set.Finite {z ∈ acceptedSet a ω | tildeP a z ∈ Set.Icc b₁ b₂} := by
  sorry
```

- [ ] **Step 2: Build with sorry**

- [ ] **Step 3: Replace `sorry`**

Strategy: the conditions `s(z) ∈ W` and `tildeP(z) ∈ [b₁, b₂]` are two
linear constraints on `(x, y) ∈ ℝ²` whose intersection is a bounded
parallelogram (since `(s, tildeP)` is invertible on `ℝ²` — its
determinant is `1 + a²`). So `(x, y)` lies in a bounded set; only
finitely many lattice points fit.

Concretely, solve for `(x, y)` in terms of `(s, tildeP)`:
```
x = (tildeP - a * s) / (1 + a²)
y = (a * tildeP + s) / (1 + a²)
```
Both `x` and `y` are bounded since `s ∈ W` and `tildeP ∈ [b₁, b₂]`
are bounded. Hence the set of admissible `(x, y) ∈ ℤ²` lies in a
bounded box, which is finite.

```lean
theorem accepted_preimage_finite
    (ha : Irrational a) (hω : 0 < ω) (b₁ b₂ : ℝ) :
    Set.Finite {z ∈ acceptedSet a ω | tildeP a z ∈ Set.Icc b₁ b₂} := by
  -- Bounds on x and y derived from the linear system.
  set D := 1 + a^2
  have hD : 0 < D := by positivity
  -- Build explicit integer bounds Mx, My via Int.floor / Int.ceil.
  obtain ⟨Mx, hMx⟩ : ∃ M : ℤ,
      ∀ z ∈ {z : ℤ × ℤ | sInternal a z ∈ W a ω ∧ tildeP a z ∈ Set.Icc b₁ b₂},
        |z.1| ≤ M := by
    sorry  -- ~15 lines: use that x = (p̃ - a·s)/D is bounded
  obtain ⟨My, hMy⟩ : ∃ M : ℤ, …  -- analogous for y
    sorry
  -- The set lies in `Finset.Icc (-Mx) Mx ×ˢ Finset.Icc (-My) My`, a finset.
  apply Set.Finite.subset (Set.Finite.prod
    (Set.finite_Icc (-Mx) Mx) (Set.finite_Icc (-My) My))
  rintro ⟨x, y⟩ ⟨hin, hp⟩
  refine ⟨?_, ?_⟩
  · exact (abs_le.mp (hMx _ ⟨hin, hp⟩)).symm.1, …
  …
```

*(This block is the most "engineering" of the file: ~80–100 lines of
linear-arithmetic manipulation. Mathlib's `Set.Finite.prod`,
`Set.finite_Icc` for `ℤ`, and `Int.floor_le`/`Int.lt_floor_add_one`
do the heavy lifting.)*

- [ ] **Step 4: Build, verify clean**

- [ ] **Step 5: Commit**

```bash
git add Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: local finiteness of projected accepted set"
```

---

## Task 6: Bi-infinite unboundedness (Section E)

**Files:**
- Modify: `Lean/CutAndProject/CutAndProject/Irrational.lean`

Paper claim (lines 1240–1257): `tildeP(A)` is unbounded above and
below. Uses the identity `tildeP = (1+a²)·x + a·s` and the density of
`s(ℤ²)` to find accepted points with `x` arbitrarily large in either
direction.

- [ ] **Step 1: Add two theorems with `sorry`**

```lean
/-! ### Section E. Bi-infinite unboundedness -/

theorem tildeP_image_unbounded_above
    (ha : Irrational a) (hω : 0 < ω) (M : ℝ) :
    ∃ z ∈ acceptedSet a ω, M < tildeP a z := by
  sorry

theorem tildeP_image_unbounded_below
    (ha : Irrational a) (hω : 0 < ω) (M : ℝ) :
    ∃ z ∈ acceptedSet a ω, tildeP a z < M := by
  sorry
```

- [ ] **Step 2: Build with sorry**

- [ ] **Step 3: Replace both sorries**

Strategy: pick a target internal value `t₀ := 0 ∈ W` (interior of `W`
since `W = [-a*ω, ω]` with `a, ω > 0`). By `dense_internal_image`,
there exist `(m, n)` with `n - a*m` close to `t₀` (so in `W`) AND
with `m` arbitrarily large (resp. small). Then
`tildeP(m, n) = (1+a²)*m + a*(n - a*m)` is dominated by `(1+a²)*m`
for large `|m|`.

```lean
theorem tildeP_image_unbounded_above
    (ha : Irrational a) (hω : 0 < ω) (M : ℝ) :
    ∃ z ∈ acceptedSet a ω, M < tildeP a z := by
  -- Choose ε small enough that any internal value within ε of 0 lies in W.
  have h0 : (0 : ℝ) ∈ interior (W a ω) := by
    -- W = Icc(-aω, ω), 0 lies strictly between since a, ω > 0.
    sorry  -- ~5 lines
  -- By density, pick (m, n) with n - a*m ∈ W and m arbitrarily large
  -- such that tildeP exceeds M.
  …
```

*(This is a “quantifier-juggling” proof; the math is direct but Lean
demands careful witness extraction. Estimate: 60–80 lines for both
theorems combined.)*

- [ ] **Step 4: Build, verify clean**

- [ ] **Step 5: Commit**

```bash
git add Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: bi-infinite unboundedness of tildeP '' acceptedSet"
```

---

## Task 7: ℤ-enumeration via `orderIsoIntOfLinearSuccPredArch` (Section F)

**Files:**
- Modify: `Lean/CutAndProject/CutAndProject/Irrational.lean`

Build `OrderIso ℤ (tildeP '' acceptedSet)` using Mathlib's
`orderIsoIntOfLinearSuccPredArch`. Inputs needed:
- `LocallyFiniteOrder` instance (from Task 5 via `ofFiniteIcc`)
- `NoMaxOrder` (from Task 6 above)
- `NoMinOrder` (from Task 6 below)
- `Nonempty` (origin `(0, 0) ∈ A`)

- [ ] **Step 1: Add definition with `sorry`**

```lean
/-! ### Section F. ℤ-enumeration of the projected accepted set -/

/-- The image of the accepted set under the projection. -/
def projectedSet : Set ℝ := tildeP a '' acceptedSet a ω

/-- Bi-infinite enumeration of the projected accepted set.
The forward map `(enumerate i)` is the i-th projected lattice point. -/
noncomputable def enumerate
    (ha : Irrational a) (hω : 0 < ω) :
    ℤ ≃o (projectedSet a ω) := by
  sorry
```

- [ ] **Step 2: Build with sorry**

- [ ] **Step 3: Replace sorry — assemble typeclass instances**

```lean
noncomputable def enumerate
    (ha : Irrational a) (hω : 0 < ω) :
    ℤ ≃o (projectedSet a ω) := by
  letI : LocallyFiniteOrder (projectedSet a ω) :=
    LocallyFiniteOrder.ofFiniteIcc (fun u v => by
      -- transfer accepted_preimage_finite from ℤ² to the subtype
      sorry)
  letI : SuccOrder (projectedSet a ω) :=
    LinearLocallyFiniteOrder.succOrder _
  letI : PredOrder (projectedSet a ω) :=
    LinearLocallyFiniteOrder.predOrder _
  haveI : NoMaxOrder (projectedSet a ω) := ⟨fun u => by
    obtain ⟨z, hz, hp⟩ := tildeP_image_unbounded_above a ω ha hω u.val
    exact ⟨⟨tildeP a z, ⟨z, hz, rfl⟩⟩, hp⟩⟩
  haveI : NoMinOrder (projectedSet a ω) := ⟨fun u => by
    obtain ⟨z, hz, hp⟩ := tildeP_image_unbounded_below a ω ha hω u.val
    exact ⟨⟨tildeP a z, ⟨z, hz, rfl⟩⟩, hp⟩⟩
  haveI : Nonempty (projectedSet a ω) :=
    ⟨⟨tildeP a (0, 0), ⟨(0, 0), by
        simp [acceptedSet, sInternal, W, mul_nonneg, hω.le]
        constructor <;> linarith [hω.le, sq_nonneg a]
      , rfl⟩⟩⟩
  exact (orderIsoIntOfLinearSuccPredArch).symm
```

- [ ] **Step 4: Build, verify clean**

- [ ] **Step 5: Commit**

```bash
git add Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: ℤ-enumeration of projected accepted set via orderIso"
```

---

## Task 8: Gap sequence and periodicity (Section G)

**Files:**
- Modify: `Lean/CutAndProject/CutAndProject/Irrational.lean`

- [ ] **Step 1: Add definitions and basic lemmas**

```lean
/-! ### Section G. Gap sequence and periodicity -/

/-- The i-th projected point (= ℓ_i in the paper). -/
noncomputable def ell (ha : Irrational a) (hω : 0 < ω) (i : ℤ) : ℝ :=
  ((enumerate a ω ha hω) i).val

/-- The i-th gap g_i := ℓ_{i+1} - ℓ_i. -/
noncomputable def gap (ha : Irrational a) (hω : 0 < ω) (i : ℤ) : ℝ :=
  ell a ω ha hω (i + 1) - ell a ω ha hω i

/-- Periodicity of the gap sequence with period λ. -/
def IsGapPeriod (ha : Irrational a) (hω : 0 < ω) (λ : ℕ) : Prop :=
  0 < λ ∧ ∀ i : ℤ, gap a ω ha hω (i + λ) = gap a ω ha hω i

/-- For an unbounded `OrderIso`, ℓ is strictly increasing. -/
lemma ell_strictMono (ha : Irrational a) (hω : 0 < ω) :
    StrictMono (ell a ω ha hω) := by
  intro i j hij
  exact (enumerate a ω ha hω).strictMono hij

/-- Each gap is strictly positive. -/
lemma gap_pos (ha : Irrational a) (hω : 0 < ω) (i : ℤ) :
    0 < gap a ω ha hω i := by
  unfold gap
  have : i < i + 1 := by linarith
  linarith [ell_strictMono a ω ha hω this]
```

- [ ] **Step 2: Build, verify clean** (no sorries needed for this task)

- [ ] **Step 3: Commit**

```bash
git add Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: gap sequence and periodicity definitions"
```

---

## Task 9: Step 2 — period lifts to lattice translation (Section H)

**Files:**
- Modify: `Lean/CutAndProject/CutAndProject/Irrational.lean`

Paper proof (lines 1296–1318): if the gap sequence has period `λ`,
the partial sum `σ := Σ g_{i+k}` for `k = 0, ..., λ-1` is independent
of `i`, so `ℓ_{i+λ} - ℓ_i = σ` and `Λ + σ = Λ`. Pick `z₀ ∈ A`,
find `z₁ ∈ A` with `tildeP(z₁) = tildeP(z₀) + σ`, set `v := z₁ - z₀`.
By Step 1 injectivity, `A + v = A`.

- [ ] **Step 1: Add helper for telescoping sum, then main theorem**

```lean
/-! ### Section H. Step 2: a finite period lifts to a lattice translation -/

private lemma telescoping_sum
    (ha : Irrational a) (hω : 0 < ω) (λ : ℕ) (hp : IsGapPeriod a ω ha hω λ)
    (i : ℤ) :
    ell a ω ha hω (i + λ) - ell a ω ha hω i =
      ell a ω ha hω (0 + λ) - ell a ω ha hω 0 := by
  sorry  -- induction on i (or on λ); ~20 lines

theorem period_lifts_to_lattice_translation
    (ha : Irrational a) (hω : 0 < ω) (λ : ℕ) (hp : IsGapPeriod a ω ha hω λ) :
    ∃ v : ℤ × ℤ, v ≠ 0 ∧
      tildeP a v > 0 ∧
      ∀ z ∈ acceptedSet a ω, z + v ∈ acceptedSet a ω := by
  sorry
```

- [ ] **Step 2: Build with sorries**

- [ ] **Step 3: Replace both sorries**

For `telescoping_sum`: induction on `i`, using `hp.2`.

For the main theorem:
- Define `σ := ell (0 + λ) - ell 0`. Using `gap_pos`, show `σ > 0`.
- Pick any `z₀ ∈ acceptedSet` (e.g. via `Nonempty` instance from Task 7).
- `tildeP z₀ + σ ∈ projectedSet` (by `Λ + σ = Λ`, formal version below).
  This means there exists `z₁ ∈ acceptedSet` with
  `tildeP z₁ = tildeP z₀ + σ`. Set `v := z₁ - z₀`.
- For any `z ∈ acceptedSet`: `tildeP z + σ` corresponds to some
  `z' ∈ acceptedSet` with `tildeP z' = tildeP (z + v)`. By
  `tildeP_injective`, `z' = z + v`, so `z + v ∈ acceptedSet`.

The "Λ + σ = Λ" step requires a small lemma:
```lean
private lemma image_shift_inv (ha : Irrational a) (hω : 0 < ω)
    (λ : ℕ) (hp : IsGapPeriod a ω ha hω λ) (i : ℤ) :
    ell a ω ha hω (i + λ) - ell a ω ha hω i =
    ell a ω ha hω (0 + λ) - ell a ω ha hω 0 := telescoping_sum a ω ha hω λ hp i
```
*(Estimate: ~110 lines for the whole section.)*

- [ ] **Step 4: Build, verify clean**

- [ ] **Step 5: Commit**

```bash
git add Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: Step 2 — period lifts to lattice translation"
```

---

## Task 10: Step 3 — density forces `v = 0` (Section I)

**Files:**
- Modify: `Lean/CutAndProject/CutAndProject/Irrational.lean`

Paper proof (lines 1320–1338): write `v = (m, n)`, `τ := s(v) = n - a*m`.
Invariance `A + v = A` gives `(W ∩ s(ℤ²)) + τ = W ∩ s(ℤ²)`. If `τ > 0`,
density of `s(ℤ²)` finds `t ∈ W ∩ s(ℤ²)` with `t > ω - τ`, but then
`t + τ > ω`, contradicting invariance. Analogously for `τ < 0`. So
`τ = 0`, i.e. `n = a*m`. Irrationality forces `m = n = 0`.

- [ ] **Step 1: Add theorem with `sorry`**

```lean
/-! ### Section I. Step 3: a non-trivial lattice translation cannot
    preserve the accepted set -/

theorem lattice_translation_must_be_zero
    (ha : Irrational a) (hω : 0 < ω) (v : ℤ × ℤ)
    (hv_inv : ∀ z ∈ acceptedSet a ω, z + v ∈ acceptedSet a ω)
    (hv_inv_neg : ∀ z ∈ acceptedSet a ω, z - v ∈ acceptedSet a ω) :
    v = 0 := by
  sorry
```

- [ ] **Step 2: Build with sorry**

- [ ] **Step 3: Replace `sorry`**

```lean
theorem lattice_translation_must_be_zero
    (ha : Irrational a) (hω : 0 < ω) (v : ℤ × ℤ)
    (hv_inv : ∀ z ∈ acceptedSet a ω, z + v ∈ acceptedSet a ω)
    (hv_inv_neg : ∀ z ∈ acceptedSet a ω, z - v ∈ acceptedSet a ω) :
    v = 0 := by
  set τ := sInternal a v
  -- Step 3a: invariance ⟹ τ = 0
  have hτ : τ = 0 := by
    by_contra hτne
    rcases lt_or_gt_of_ne hτne with hτneg | hτpos
    · -- τ < 0: pick t ∈ W ∩ s(ℤ²) with t < -a*ω - τ; then t + τ < -a*ω
      obtain ⟨t, ⟨w, hw_eq⟩, ht_W, ht_close⟩ :=
        (dense_internal_image a ha).exists_between
          (-(a * ω) - τ) (-(a * ω))
          (by linarith)
      -- contradicts hv_inv_neg
      sorry
    · -- τ > 0: symmetric
      sorry
  -- Step 3b: τ = 0 ⟹ n = a*m. Irrationality forces m = n = 0.
  have hm_n : (v.2 : ℝ) = a * (v.1 : ℝ) := by
    have : (v.2 : ℝ) - a * (v.1 : ℝ) = 0 := by simpa [sInternal] using hτ
    linarith
  -- If m ≠ 0, then a = n/m ∈ ℚ, contradicting `ha`.
  by_cases hm : v.1 = 0
  · -- v.1 = 0 ⟹ v.2 = 0 (from hm_n with a*0 = 0)
    have : (v.2 : ℝ) = 0 := by rw [hm_n, hm]; ring
    have hn : v.2 = 0 := by exact_mod_cast this
    exact Prod.mk.injEq .. |>.mpr ⟨hm, hn⟩
  · exfalso
    apply ha
    refine ⟨(v.2 : ℚ) / (v.1 : ℚ), ?_⟩
    push_cast
    field_simp at hm_n ⊢
    linarith
```

*(Estimate: ~80 lines including the two density-application sub-steps.)*

- [ ] **Step 4: Build, verify clean**

- [ ] **Step 5: Commit**

```bash
git add Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: Step 3 — only the zero translation preserves accepted set"
```

---

## Task 11: Main theorem `prop_irrational` (Section J)

**Files:**
- Modify: `Lean/CutAndProject/CutAndProject/Irrational.lean`

- [ ] **Step 1: Add main theorem with proof (no sorry needed)**

```lean
/-! ### Section J. Main theorem: aperiodicity for irrational slope -/

/-- **Proposition 1 (paper, Section "The Irrational Case").**
For `a ∈ ℝ_{>0} ∖ ℚ` and `ω > 0`, the projected gap sequence has
no finite period. -/
theorem prop_irrational
    (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) :
    ¬ ∃ λ : ℕ, IsGapPeriod a ω ha hω λ := by
  rintro ⟨λ, hp⟩
  obtain ⟨v, hv_ne, hv_pos, hv_inv⟩ :=
    period_lifts_to_lattice_translation a ω ha hω λ hp
  -- Reverse-direction invariance: from period -λ, or directly
  -- by re-running the argument with σ → -σ.
  have hv_inv_neg : ∀ z ∈ acceptedSet a ω, z - v ∈ acceptedSet a ω := by
    sorry  -- ~10 lines: same Step-1 injectivity argument applied to -σ
  exact hv_ne (lattice_translation_must_be_zero a ω ha hω v hv_inv hv_inv_neg)
```

- [ ] **Step 2: Replace the small inner sorry** with the symmetric argument from Task 9.

- [ ] **Step 3: Build, verify 0 sorry / 0 warnings**

Run: `cd Lean/CutAndProject && lake build`

- [ ] **Step 4: Commit**

```bash
git add Lean/CutAndProject/CutAndProject/Irrational.lean
git commit -m "Lean: prop_irrational — aperiodicity for irrational slope"
```

---

## Task 12: Final verification

**Files:** none new — full-project sanity check.

- [ ] **Step 1: Full clean build**

```bash
cd Lean/CutAndProject
lake clean
lake build
```
Expected: `Build completed successfully.` No `sorry` warnings, no
`unused variable` warnings, no `linter` warnings.

- [ ] **Step 2: Verify zero sorry**

```bash
grep -nR "sorry" Lean/CutAndProject/CutAndProject/Irrational.lean
```
Expected: no output.

- [ ] **Step 3: Line count sanity check**

```bash
wc -l Lean/CutAndProject/CutAndProject/Irrational.lean
```
Expected: ~400–700 lines. If much less: proofs likely incomplete.
If much more: too verbose; consider extracting helper lemmas.

- [ ] **Step 4: Update memory record**

Update `set_valued_period_design.md`: `Lean N lines, +1 file Irrational.lean`,
note "irrational case formalized, 0 sorry".

---

## Task 13 (optional): Update paper Section 9

**Files:**
- Modify: `LaTeX/rational_cut_and_project_gap_periods.tex`

Paper currently advertises rational-only formalization (line ~1370:
"approximately 2,850 lines"). If you ship the irrational case, update:

- [ ] **Step 1: Update line count and add reference to Irrational.lean**

In Section 9 ("Machine-Checked Formalization"), add one paragraph:

> The aperiodicity result for irrational slopes
> (Proposition~\ref{prop:irrational}) is formalized in
> \texttt{Irrational.lean} (~N lines, no \texttt{sorry}), under
> the same companion repository. Together with the rational
> formalization, this completes the machine-checked period
> dichotomy of Remark~\ref{rem:dichotomy}.

- [ ] **Step 2: Recompile LaTeX, sanity-check**

- [ ] **Step 3: Commit (paper + Lean together)**

```bash
git add LaTeX/rational_cut_and_project_gap_periods.tex
git commit -m "paper: advertise Lean formalization of the irrational case"
```

---

## Task summary table

| # | Block | New lines | Risk |
|---|---|---|---|
| 1  | Skeleton + build wiring         |  ~20 | low |
| 2  | Definitions (Section A)         |  ~30 | low |
| 3  | Step 1: tildeP injective        |  ~25 | low |
| 4  | Kronecker density bridge        |  ~40 | medium |
| 5  | Local finiteness                |  ~90 | medium-high |
| 6  | Bi-infinite unboundedness       |  ~80 | medium |
| 7  | ℤ-enumeration via orderIso      |  ~40 | low (Mathlib does it) |
| 8  | Gap sequence + periodicity      |  ~50 | low |
| 9  | Step 2: period → lattice transl.| ~110 | medium |
| 10 | Step 3: density forces v=0      |  ~80 | medium |
| 11 | Main theorem prop_irrational    |  ~40 | low |
| 12 | Final verification              |   —  | — |
| 13 | (optional) Paper update         |   —  | — |
| **Total Lean** | | **~605** | |

Realistic estimate: **5–7 working days**, given familiarity with
the existing Basic.lean style. If Task 5 (local finiteness) hits
unexpected Mathlib API gaps, add 1–2 days.
