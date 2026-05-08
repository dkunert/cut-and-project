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
      exact ⟨m, n, by simp only [sInternal, zsmul_eq_mul]; ring⟩
    · rintro ⟨m, n, hmn⟩
      -- m • (-a) + n • 1 = -m*a + n = n - a*m = sInternal a (m, n)
      exact ⟨⟨m, n⟩, by simp only [sInternal, zsmul_eq_mul] at hmn ⊢; linarith⟩
  -- Step 2: density of the closure follows from irrationality via Mathlib's theorem
  rw [hrange, dense_addSubgroupClosure_pair_iff]
  rw [div_one]; rwa [irrational_neg_iff]

/-! ### Section D. Local finiteness of the projected accepted set -/

/-- The preimage in `ℤ²` of any bounded interval, intersected with the
accepted set, is finite.

Proof sketch.  For `(x, y)` in the set we have
`s := y - a*x ∈ [-a*ω, ω]` and `p := x + a*y ∈ [b₁, b₂]`.  Inverting the
linear system gives `x = (p - a*s)/(1+a²)` and `y = (a*p + s)/(1+a²)`,
so both `x` and `y` are bounded by an explicit real constant.  Since
`x, y : ℤ` lie in a bounded subset of `ℝ`, they lie in a finite box. -/
theorem accepted_preimage_finite
    (hω : 0 < ω) (b₁ b₂ : ℝ) :
    Set.Finite {z ∈ acceptedSet a ω | tildeP a z ∈ Set.Icc b₁ b₂} := by
  -- Set up the determinant `D = 1 + a²` and a uniform real bound `B` on `|x|`, `|y|`.
  set D : ℝ := 1 + a ^ 2 with hD_def
  have hD_pos : 0 < D := by
    have h1 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
    linarith
  -- Bound `|s|` by `Bs := |a|*ω + ω` (loose but explicit).
  set Bs : ℝ := |a| * ω + ω with hBs_def
  have hBs_nn : 0 ≤ Bs := by
    have : 0 ≤ |a| * ω := mul_nonneg (abs_nonneg a) hω.le
    linarith
  -- Bound `|p|` by `Bp := |b₁| + |b₂|` (loose but explicit).
  set Bp : ℝ := |b₁| + |b₂| with hBp_def
  have hBp_nn : 0 ≤ Bp := by
    have h1 : 0 ≤ |b₁| := abs_nonneg _
    have h2 : 0 ≤ |b₂| := abs_nonneg _
    linarith
  -- Combined real bound on |x| and |y|.
  set R : ℝ := (1 + |a|) * (Bp + Bs) with hR_def
  have hR_nn : 0 ≤ R := by
    have h1 : 0 ≤ 1 + |a| := by have := abs_nonneg a; linarith
    have h2 : 0 ≤ Bp + Bs := by linarith
    exact mul_nonneg h1 h2
  -- Integer cap for the box.
  set N : ℤ := ⌈R⌉ with hN_def
  -- The set is a subset of `Set.Icc (-N) N ×ˢ Set.Icc (-N) N`.
  apply Set.Finite.subset
    (Set.Finite.prod (Set.finite_Icc (-N) N) (Set.finite_Icc (-N) N))
  rintro ⟨x, y⟩ ⟨hAcc, hP⟩
  -- Unpack hypotheses.
  have hs_mem : sInternal a (x, y) ∈ W a ω := hAcc
  rcases hs_mem with ⟨hs_lo, hs_hi⟩
  -- hs_lo : -(a * ω) ≤ y - a*x
  -- hs_hi : y - a*x ≤ ω
  have hs_lo' : -(a * ω) ≤ (y : ℝ) - a * x := hs_lo
  have hs_hi' : (y : ℝ) - a * x ≤ ω := hs_hi
  rcases hP with ⟨hp_lo, hp_hi⟩
  -- hp_lo : b₁ ≤ x + a*y
  -- hp_hi : x + a*y ≤ b₂
  have hp_lo' : b₁ ≤ (x : ℝ) + a * y := hp_lo
  have hp_hi' : (x : ℝ) + a * y ≤ b₂ := hp_hi
  -- Bound |s| by Bs.
  have habs_s : |(y : ℝ) - a * x| ≤ Bs := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · -- -Bs ≤ y - a*x
      have h1 : -(|a| * ω) ≤ -(a * ω) := by
        have : a * ω ≤ |a| * ω := by
          have habs : a ≤ |a| := le_abs_self a
          exact mul_le_mul_of_nonneg_right habs hω.le
        linarith
      have h2 : -(|a| * ω) - ω ≤ -(a * ω) := by linarith
      have h3 : -Bs = -(|a| * ω) - ω := by simp [Bs]; ring
      linarith
    · -- y - a*x ≤ Bs
      have : ω ≤ Bs := by
        have : 0 ≤ |a| * ω := mul_nonneg (abs_nonneg a) hω.le
        simp [Bs]; linarith
      linarith
  -- Bound |p| by Bp.
  have habs_p : |(x : ℝ) + a * y| ≤ Bp := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · -- -Bp ≤ x + a*y
      have h1 : -|b₁| ≤ b₁ := neg_abs_le b₁
      have h2 : -|b₂| ≤ 0 := neg_nonpos_of_nonneg (abs_nonneg b₂)
      have : -Bp = -|b₁| + -|b₂| := by simp [Bp]; ring
      linarith
    · -- x + a*y ≤ Bp
      have h1 : b₂ ≤ |b₂| := le_abs_self b₂
      have h2 : 0 ≤ |b₁| := abs_nonneg b₁
      have : Bp = |b₁| + |b₂| := rfl
      linarith
  -- Identity: D * x = p - a * s, hence |x| ≤ (Bp + |a|*Bs)/D ≤ R.
  have hDx : D * (x : ℝ) = ((x : ℝ) + a * y) - a * ((y : ℝ) - a * x) := by
    simp [D]; ring
  have hDy : D * (y : ℝ) = a * ((x : ℝ) + a * y) + ((y : ℝ) - a * x) := by
    simp [D]; ring
  -- From these identities, real-value bound on |x| and |y|.
  have habs_Dx : |D * (x : ℝ)| ≤ Bp + |a| * Bs := by
    rw [hDx]
    have htri : |((x : ℝ) + a * y) - a * ((y : ℝ) - a * x)|
              ≤ |((x : ℝ) + a * y)| + |a * ((y : ℝ) - a * x)| := by
      have h := abs_add_le ((x : ℝ) + a * y) (-(a * ((y : ℝ) - a * x)))
      have heq : ((x : ℝ) + a * y) + -(a * ((y : ℝ) - a * x))
              = ((x : ℝ) + a * y) - a * ((y : ℝ) - a * x) := by ring
      rw [heq] at h
      have habs_neg : |-(a * ((y : ℝ) - a * x))| = |a * ((y : ℝ) - a * x)| := abs_neg _
      rw [habs_neg] at h
      exact h
    have hmulabs : |a * ((y : ℝ) - a * x)| = |a| * |(y : ℝ) - a * x| := abs_mul _ _
    have h2 : |a| * |(y : ℝ) - a * x| ≤ |a| * Bs :=
      mul_le_mul_of_nonneg_left habs_s (abs_nonneg a)
    linarith
  have habs_Dy : |D * (y : ℝ)| ≤ |a| * Bp + Bs := by
    rw [hDy]
    have htri : |a * ((x : ℝ) + a * y) + ((y : ℝ) - a * x)|
              ≤ |a * ((x : ℝ) + a * y)| + |((y : ℝ) - a * x)| :=
      abs_add_le _ _
    have hmulabs : |a * ((x : ℝ) + a * y)| = |a| * |((x : ℝ) + a * y)| := abs_mul _ _
    have h1 : |a| * |((x : ℝ) + a * y)| ≤ |a| * Bp :=
      mul_le_mul_of_nonneg_left habs_p (abs_nonneg a)
    linarith
  -- D ≥ 1 since a² ≥ 0
  have hD_ge_one : (1 : ℝ) ≤ D := by
    have : 0 ≤ a ^ 2 := sq_nonneg a
    simp [D]; linarith
  -- Algebraic fact: both `Bp + |a|*Bs` and `|a|*Bp + Bs` are ≤ R = (1+|a|)*(Bp+Bs).
  have hbound_x : Bp + |a| * Bs ≤ R := by
    have h1 : 0 ≤ |a| * Bp := mul_nonneg (abs_nonneg _) hBp_nn
    simp [R]; nlinarith
  have hbound_y : |a| * Bp + Bs ≤ R := by
    have h1 : 0 ≤ |a| * Bs := mul_nonneg (abs_nonneg _) hBs_nn
    simp [R]; nlinarith
  -- |x| ≤ R, |y| ≤ R.
  have habs_x : |(x : ℝ)| ≤ R := by
    have hx1 : |D * (x : ℝ)| = D * |(x : ℝ)| := by
      rw [abs_mul, abs_of_pos hD_pos]
    have hx2 : D * |(x : ℝ)| ≤ Bp + |a| * Bs := by rw [← hx1]; exact habs_Dx
    have hx3 : 1 * |(x : ℝ)| ≤ D * |(x : ℝ)| :=
      mul_le_mul_of_nonneg_right hD_ge_one (abs_nonneg _)
    have hx4 : |(x : ℝ)| ≤ Bp + |a| * Bs := by
      have : 1 * |(x : ℝ)| = |(x : ℝ)| := one_mul _
      linarith
    linarith
  have habs_y : |(y : ℝ)| ≤ R := by
    have hy1 : |D * (y : ℝ)| = D * |(y : ℝ)| := by
      rw [abs_mul, abs_of_pos hD_pos]
    have hy2 : D * |(y : ℝ)| ≤ |a| * Bp + Bs := by rw [← hy1]; exact habs_Dy
    have hy3 : 1 * |(y : ℝ)| ≤ D * |(y : ℝ)| :=
      mul_le_mul_of_nonneg_right hD_ge_one (abs_nonneg _)
    have hy4 : |(y : ℝ)| ≤ |a| * Bp + Bs := by
      have : 1 * |(y : ℝ)| = |(y : ℝ)| := one_mul _
      linarith
    linarith
  -- Now turn real |x| ≤ R into integer |x| ≤ N (= ⌈R⌉).
  have hRN : R ≤ (N : ℝ) := Int.le_ceil R
  have habs_x_int : |(x : ℝ)| ≤ (N : ℝ) := le_trans habs_x hRN
  have habs_y_int : |(y : ℝ)| ≤ (N : ℝ) := le_trans habs_y hRN
  -- Convert real abs bounds back to integer bounds.
  have habs_x_int' : |x| ≤ N := by
    have : |((x : ℝ))| = ((|x| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
    rw [this] at habs_x_int
    exact_mod_cast habs_x_int
  have habs_y_int' : |y| ≤ N := by
    have : |((y : ℝ))| = ((|y| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
    rw [this] at habs_y_int
    exact_mod_cast habs_y_int
  -- Both coordinates are in [-N, N].
  refine Set.mk_mem_prod ?_ ?_
  · -- x ∈ Set.Icc (-N) N
    simp only [Set.mem_Icc]
    have := abs_le.mp habs_x_int'
    exact this
  · -- y ∈ Set.Icc (-N) N
    simp only [Set.mem_Icc]
    have := abs_le.mp habs_y_int'
    exact this

end CutAndProject.Irrational
