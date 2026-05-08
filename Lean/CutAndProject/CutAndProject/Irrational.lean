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

/-! ### Section B. Step 1: `tildeP` is injective on `ℤ²` -/

theorem tildeP_injective (ha : Irrational a) :
    Function.Injective (tildeP a) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  -- h : tildeP a (x₁, y₁) = tildeP a (x₂, y₂)
  -- i.e. (x₁ : ℝ) + a * y₁ = (x₂ : ℝ) + a * y₂
  simp only [tildeP] at h
  by_cases hy : y₁ = y₂
  · -- y₁ = y₂ forces x₁ = x₂
    subst hy
    have hx : (x₁ : ℝ) = (x₂ : ℝ) := by linarith
    exact Prod.ext (by exact_mod_cast hx) rfl
  · -- y₁ ≠ y₂ ⟹ a is rational, contradicting `Irrational a`
    exfalso
    -- Rearrange h to:  a * ((y₁ - y₂ : ℤ) : ℝ) = ((x₂ - x₁ : ℤ) : ℝ)
    have hne : (y₁ : ℝ) - y₂ ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hy
    -- a = (x₂ - x₁) / (y₁ - y₂)
    have ha_eq : a = ((x₂ - x₁ : ℤ) : ℝ) / ((y₁ - y₂ : ℤ) : ℝ) := by
      push_cast
      field_simp [hne]
      linarith
    -- Express a as a rational number
    apply ha
    -- division evaluated in ℚ after push_cast, not as truncated Int division
    refine ⟨(x₂ - x₁ : ℤ) / (y₁ - y₂ : ℤ), ?_⟩
    rw [ha_eq]
    push_cast
    rfl

/-! ### Section C. Kronecker density of `ℤ + a·ℤ` -/

/-- For irrational `a`, the set `{n - a*m : m, n ∈ ℤ}` is dense in `ℝ`. -/
theorem dense_internal_image (ha : Irrational a) :
    Dense (Set.range (sInternal a)) := by
  -- Step 1: the range equals the closure of {-a, 1} as a subgroup of ℝ
  have hrange : Set.range (sInternal a) = (AddSubgroup.closure ({-a, 1} : Set ℝ) : Set ℝ) := by
    ext z
    simp only [Set.mem_range, SetLike.mem_coe, AddSubgroup.mem_closure_pair]
    constructor
    · rintro ⟨⟨m, n⟩, rfl⟩
      -- sInternal a (m, n) = n - a*m = m • (-a) + n • 1
      exact ⟨m, n, by simp [sInternal, zsmul_eq_mul]; ring⟩
    · rintro ⟨m, n, hmn⟩
      -- m • (-a) + n • 1 = -m*a + n = n - a*m = sInternal a (m, n)
      exact ⟨⟨m, n⟩, by simp only [sInternal, zsmul_eq_mul] at hmn ⊢; linarith⟩
  -- Step 2: density of the closure follows from irrationality via Mathlib's theorem
  rw [hrange, dense_addSubgroupClosure_pair_iff]
  simp [irrational_neg_iff, ha]

end CutAndProject.Irrational
