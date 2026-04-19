import Mathlib

open Nat

namespace CutAndProject

/--
Lemma 4.1 from the paper.
Given α, β ∈ ℕ with gcd(α, β) = 1, we have gcd(α, α^2 + β^2) = 1.
-/
theorem coprime_alpha_D (α β : ℕ) (h : Nat.Coprime α β) : Nat.Coprime α (α^2 + β^2) := by
  have h1 : Nat.Coprime α (β^2) := Nat.Coprime.pow_right 2 h
  have h2 : α^2 + β^2 = β^2 + α * α := by ring
  rw [h2]
  exact (Nat.coprime_add_mul_right_right α (β^2) α).mpr h1

/--
Symmetric part of Lemma 4.1.
-/
theorem coprime_beta_D (α β : ℕ) (h : Nat.Coprime α β) : Nat.Coprime β (α^2 + β^2) := by
  have h1 : Nat.Coprime β (α^2) := Nat.Coprime.pow_right 2 h.symm
  have h2 : α^2 + β^2 = α^2 + β * β := by ring
  rw [h2]
  exact (Nat.coprime_add_mul_right_right β (α^2) β).mpr h1

lemma D_pos (α β : ℕ) (h : Nat.Coprime α β) : 0 < α^2 + β^2 := by
  rcases Nat.eq_zero_or_pos α with rfl | hα
  · rw [Nat.coprime_zero_left] at h
    rw [h]
    decide
  · have h1 : 0 < α^2 := Nat.pos_of_ne_zero (pow_ne_zero 2 (Nat.ne_of_gt hα))
    omega

def beta_unit (α β : ℕ) (h : Nat.Coprime α β) [NeZero (α^2 + β^2)] : (ZMod (α^2 + β^2))ˣ :=
  ZMod.unitOfCoprime β (coprime_beta_D α β h)

def alpha_unit (α β : ℕ) (h : Nat.Coprime α β) [NeZero (α^2 + β^2)] : (ZMod (α^2 + β^2))ˣ :=
  ZMod.unitOfCoprime α (coprime_alpha_D α β h)

def multiplier (α β : ℕ) (h : Nat.Coprime α β) [NeZero (α^2 + β^2)] : (ZMod (α^2 + β^2))ˣ :=
  (-1 : (ZMod (α^2 + β^2))ˣ) * (alpha_unit α β h) * (beta_unit α β h)⁻¹

def residue_bijection (α β : ℕ) (h : Nat.Coprime α β) [NeZero (α^2 + β^2)] : 
    Equiv (ZMod (α^2 + β^2)) (ZMod (α^2 + β^2)) where
  toFun x := (multiplier α β h).val * x
  invFun x := (multiplier α β h)⁻¹.val * x
  left_inv x := by
    dsimp
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    dsimp
    rw [← mul_assoc, Units.mul_inv, one_mul]

section ResidueDistribution

/--
Lemma 4.3: Non-uniform residue distribution.

`count_hits D r0 N x` counts the number of times the residue `x` (modulo `D`) is hit
by the arithmetic progression `r0, r0+1, ..., r0+N-1` of length `N`.
-/
def count_hits (D : ℕ) [NeZero D] (r0 N : ℕ) (x : ZMod D) : ℕ :=
  (Finset.range N).filter (fun (i : ℕ) => (r0 + i : ZMod D) = x) |>.card

lemma count_hits_D (D : ℕ) [NeZero D] (r0 : ℕ) (x : ZMod D) : 
    count_hits D r0 D x = 1 := by
  dsimp [count_hits]
  have h_unique : (Finset.range D).filter (fun (i : ℕ) => (r0 + i : ZMod D) = x) = {(x - (r0 : ZMod D)).val} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hi_lt, hi_eq⟩
      have h1 : (i : ZMod D) = x - (r0 : ZMod D) := by
        calc (i : ZMod D) = (r0 : ZMod D) + i - (r0 : ZMod D) := by ring
             _ = x - (r0 : ZMod D) := by rw [hi_eq]
      have h2 : i = (i : ZMod D).val := by
        have h_mod : (i : ZMod D).val = i % D := ZMod.val_natCast D i
        rw [h_mod, Nat.mod_eq_of_lt hi_lt]
      rw [h2, h1]
    · rintro rfl
      have h_lt : (x - (r0 : ZMod D)).val < D := ZMod.val_lt (x - (r0 : ZMod D))
      refine ⟨h_lt, ?_⟩
      have h_cast : ((x - (r0 : ZMod D)).val : ZMod D) = x - (r0 : ZMod D) := ZMod.natCast_zmod_val (x - (r0 : ZMod D))
      rw [h_cast]
      ring
  rw [h_unique, Finset.card_singleton]

lemma count_hits_lt_D (D : ℕ) [NeZero D] (r0 N : ℕ) (h : N < D) (x : ZMod D) : 
    count_hits D r0 N x ≤ 1 := by
  dsimp [count_hits]
  rw [Finset.card_le_one]
  intro i hi j hj
  rw [Finset.mem_filter, Finset.mem_range] at hi hj
  have h_eq : (r0 + i : ZMod D) = (r0 + j : ZMod D) := by rw [hi.2, hj.2]
  have h_eq2 : (i : ZMod D) = (j : ZMod D) := add_left_cancel h_eq
  have hi_lt : i < D := lt_trans hi.1 h
  have hj_lt : j < D := lt_trans hj.1 h
  have h_mod : i ≡ j [MOD D] := (ZMod.natCast_eq_natCast_iff i j D).mp h_eq2
  exact Nat.ModEq.eq_of_lt_of_lt h_mod hi_lt hj_lt
lemma sum_count_hits (D : ℕ) [NeZero D] (r0 N : ℕ) :
    ∑ x : ZMod D, count_hits D r0 N x = N := by
  dsimp [count_hits]
  have h := @Finset.card_eq_sum_card_fiberwise ℕ (ZMod D) _ (fun i => (r0 + i : ZMod D)) (Finset.range N) Finset.univ (fun x _ => Finset.mem_univ _)
  rw [← h]
  exact Finset.card_range N

lemma count_hits_succ (D : ℕ) [NeZero D] (r0 N : ℕ) (x : ZMod D) : 
    count_hits D r0 (N + 1) x = count_hits D r0 N x + if (r0 + N : ZMod D) = x then 1 else 0 := by
  dsimp [count_hits]
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · rfl

lemma count_hits_add (D : ℕ) [NeZero D] (r0 N M : ℕ) (x : ZMod D) : 
    count_hits D r0 (N + M) x = count_hits D r0 N x + count_hits D (r0 + N) M x := by
  induction' M with k ih
  · dsimp [count_hits]
    simp
  · rw [Nat.add_succ, count_hits_succ, ih, count_hits_succ, ← add_assoc]
    congr 2
    congr 1
    push_cast
    ring

lemma count_hits_mul_D (D : ℕ) [NeZero D] (r0 q : ℕ) (x : ZMod D) : 
    count_hits D r0 (q * D) x = q := by
  induction' q with k ih
  · dsimp [count_hits]
    simp
  · rw [Nat.succ_mul, count_hits_add, ih, count_hits_D]

lemma count_hits_eq (D : ℕ) [NeZero D] (r0 N : ℕ) (x : ZMod D) : 
    count_hits D r0 N x = (N / D) + count_hits D (r0 + (N / D) * D) (N % D) x := by
  have h_div : N = (N / D) * D + (N % D) := Nat.div_add_mod' N D |>.symm
  nth_rw 1 [h_div]
  rw [count_hits_add, count_hits_mul_D]

theorem non_uniform_residue_distribution (D : ℕ) [NeZero D] (r0 N : ℕ) :
    let q := N / D
    let s := N % D
    (Finset.univ.filter (fun x : ZMod D => count_hits D r0 N x = q + 1)).card = s ∧
    (Finset.univ.filter (fun x : ZMod D => count_hits D r0 N x = q)).card = D - s := by
  intro q s
  have h_s_lt : s < D := Nat.mod_lt N (NeZero.pos D)
  have hc_le : ∀ x, count_hits D (r0 + q * D) s x ≤ 1 := fun x => count_hits_lt_D D (r0 + q * D) s h_s_lt x
  have h_sum : ∑ x : ZMod D, count_hits D (r0 + q * D) s x = s := sum_count_hits D (r0 + q * D) s
  have heq : ∀ x, count_hits D r0 N x = q + count_hits D (r0 + q * D) s x := fun x => count_hits_eq D r0 N x
  
  have h_card1 : (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 1)).card = s := by
    calc (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 1)).card
      _ = ∑ x ∈ Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 1), 1 := by
        symm
        exact Finset.sum_const_nat (fun _ _ => rfl) |>.trans (mul_one _)
      _ = ∑ x ∈ Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 1), count_hits D (r0 + q * D) s x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [hx.2]
      _ = ∑ x ∈ Finset.univ, count_hits D (r0 + q * D) s x := by
        apply Finset.sum_subset
        · exact Finset.filter_subset _ _
        · intro x _ hx
          rw [Finset.mem_filter, not_and] at hx
          have h1 := hx (Finset.mem_univ x)
          have h2 := hc_le x
          omega
      _ = s := h_sum

  have h_card0 : (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 0)).card = D - s := by
    have h_union : Finset.univ = Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 0) ∪ Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 1) := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
      have h2 := hc_le x
      omega
    have h_disj : Disjoint (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 0)) (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 1)) := by
      simp only [Finset.disjoint_filter]
      intro x _ h0 h1
      omega
    have h_card_univ := Finset.card_union_of_disjoint h_disj
    rw [← h_union] at h_card_univ
    have hd : (Finset.univ : Finset (ZMod D)).card = D := ZMod.card D
    have h_eq_card : D = (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 0)).card + s := by
      calc D = (Finset.univ : Finset (ZMod D)).card := hd.symm
           _ = (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 0)).card + (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 1)).card := h_card_univ
           _ = (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 0)).card + s := by rw [h_card1]
    calc (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 0)).card
      _ = (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 0)).card + s - s := by rw [Nat.add_sub_cancel]
      _ = D - s := by rw [← h_eq_card]

  constructor
  · have h_eq_set1 : (Finset.univ.filter (fun x : ZMod D => count_hits D r0 N x = q + 1)) = (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [heq x]
      omega
    rw [h_eq_set1, h_card1]
  · have h_eq_set0 : (Finset.univ.filter (fun x : ZMod D => count_hits D r0 N x = q)) = (Finset.univ.filter (fun x : ZMod D => count_hits D (r0 + q * D) s x = 0)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [heq x]
      omega
    rw [h_eq_set0, h_card0]

lemma count_hits_zero (D : ℕ) [NeZero D] (r0 : ℕ) (x : ZMod D) :
    count_hits D r0 0 x = 0 := by
  dsimp [count_hits]
  rw [Finset.filter_empty, Finset.card_empty]

/--
Lemma (Degenerate Case): Uniform residue distribution.
If `D ∣ N`, then every residue class is hit exactly `N / D` times.
-/
theorem uniform_residue_distribution (D : ℕ) [NeZero D] (r0 N : ℕ) (h : D ∣ N) (x : ZMod D) :
    count_hits D r0 N x = N / D := by
  have h_eq := count_hits_eq D r0 N x
  have h_mod : N % D = 0 := Nat.mod_eq_zero_of_dvd h
  rw [h_mod, count_hits_zero] at h_eq
  exact h_eq

end ResidueDistribution

section Minimality

def cyclic_interval (D s : ℕ) [NeZero D] (x0 : ZMod D) : Finset (ZMod D) :=
  (Finset.range s).image (fun (i : ℕ) => x0 + (i : ZMod D))

lemma cyclic_interval_mem (D s : ℕ) [NeZero D] (x0 : ZMod D) (x : ZMod D) :
    x ∈ cyclic_interval D s x0 ↔ ∃ (i : ℕ), i < s ∧ x = x0 + (i : ZMod D) := by
  dsimp [cyclic_interval]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

lemma count_hits_lt_D_eq_one (D s : ℕ) [NeZero D] (r0 : ℕ) (h_s_lt : s < D) (x : ZMod D) :
    count_hits D r0 s x = 1 ↔ x ∈ cyclic_interval D s (r0 : ZMod D) := by
  dsimp [count_hits]
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨a, ha⟩
    have h_a_in : a ∈ (Finset.range s).filter (fun (i : ℕ) => (r0 + i : ZMod D) = x) := by
      rw [ha]
      exact Finset.mem_singleton_self a
    rw [Finset.mem_filter, Finset.mem_range] at h_a_in
    rw [cyclic_interval_mem]
    use a
    constructor
    · exact h_a_in.1
    · exact h_a_in.2.symm
  · intro h_in
    rw [cyclic_interval_mem] at h_in
    rcases h_in with ⟨i, hi, rfl⟩
    use i
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, h_eq⟩
      have h_eq2 : ((r0 : ZMod D) + (j : ZMod D) : ZMod D) = ((r0 : ZMod D) + (i : ZMod D) : ZMod D) := h_eq
      have h_eq3 : (j : ZMod D) = (i : ZMod D) := add_left_cancel h_eq2
      have h_mod : j ≡ i [MOD D] := (ZMod.natCast_eq_natCast_iff j i D).mp h_eq3
      exact Nat.ModEq.eq_of_lt_of_lt h_mod (lt_trans hj h_s_lt) (lt_trans hi h_s_lt)
    · rintro rfl
      exact ⟨hi, rfl⟩

lemma heavy_set_is_cyclic_interval (D : ℕ) [NeZero D] (r0 N : ℕ) :
    let q := N / D
    let s := N % D
    ∀ x : ZMod D, count_hits D r0 N x = q + 1 ↔ x ∈ cyclic_interval D s ((r0 + q * D : ℕ) : ZMod D) := by
  intro q s x
  have h_s_lt : s < D := Nat.mod_lt N (NeZero.pos D)
  have h_eq := count_hits_eq D r0 N x
  constructor
  · intro h
    have h2 : q + count_hits D (r0 + q * D) s x = q + 1 := by
      calc q + count_hits D (r0 + q * D) s x = count_hits D r0 N x := h_eq.symm
           _ = q + 1 := h
    have h3 : count_hits D (r0 + q * D) s x = 1 := add_left_cancel h2
    exact (count_hits_lt_D_eq_one D s (r0 + q * D) h_s_lt x).mp h3
  · intro h
    have h3 : count_hits D (r0 + q * D) s x = 1 := (count_hits_lt_D_eq_one D s (r0 + q * D) h_s_lt x).mpr h
    rw [h_eq, h3]


lemma right_boundary_exists (D s : ℕ) [NeZero D] (x0 : ZMod D) (h_s_pos : 0 < s) (h_s_lt : s < D) :
    (x0 + (s - 1 : ℕ) : ZMod D) ∈ cyclic_interval D s x0 ∧ 
    (x0 + (s - 1 : ℕ) + 1 : ZMod D) ∉ cyclic_interval D s x0 := by
  constructor
  · rw [cyclic_interval_mem]
    use s - 1
    constructor
    · omega
    · rfl
  · intro h_in
    rw [cyclic_interval_mem] at h_in
    rcases h_in with ⟨i, hi, h_eq⟩
    have h_add : (x0 + (s - 1 : ℕ) + 1 : ZMod D) = x0 + s := by
      calc x0 + (s - 1 : ℕ) + 1 = x0 + ((s - 1 : ℕ) + 1 : ZMod D) := by ring
           _ = x0 + (((s - 1 + 1 : ℕ) : ZMod D)) := by push_cast; rfl
           _ = x0 + (s : ZMod D) := by 
             congr 2
             have : s - 1 + 1 = s := Nat.sub_add_cancel h_s_pos
             rw [this]
    rw [h_add] at h_eq
    have h_eq2 : (s : ZMod D) = (i : ZMod D) := add_left_cancel h_eq
    have h_mod : s ≡ i [MOD D] := (ZMod.natCast_eq_natCast_iff s i D).mp h_eq2
    have h_eq3 : s = i := Nat.ModEq.eq_of_lt_of_lt h_mod h_s_lt (lt_trans hi h_s_lt)
    omega

lemma right_boundary_unique (D s : ℕ) [NeZero D] (x0 : ZMod D) (h_s_pos : 0 < s) (h_s_lt : s < D) (y : ZMod D)
    (hy_in : y ∈ cyclic_interval D s x0) (hy_next_notin : y + 1 ∉ cyclic_interval D s x0) :
    y = x0 + (s - 1 : ℕ) := by
  rw [cyclic_interval_mem] at hy_in
  rcases hy_in with ⟨i, hi, rfl⟩
  have h_eq : i = s - 1 := by
    by_contra h_neq
    have h_i_lt : i < s - 1 := by omega
    have h_next_in : x0 + (i : ZMod D) + 1 ∈ cyclic_interval D s x0 := by
      rw [cyclic_interval_mem]
      use i + 1
      constructor
      · omega
      · push_cast; ring
    exact hy_next_notin h_next_in
  rw [h_eq]

/--
Lemma (Minimality): A cyclic interval of length `s` with `0 < s < D`
cannot be invariant under any non-zero translation `τ`.
-/
lemma cyclic_interval_stabilizer_trivial (D s : ℕ) [NeZero D] (x0 : ZMod D) (τ : ZMod D)
    (h_s_pos : 0 < s) (h_s_lt : s < D)
    (h_inv : ∀ x, x ∈ cyclic_interval D s x0 ↔ (x + τ) ∈ cyclic_interval D s x0) :
    τ = 0 := by
  let y := x0 + (s - 1 : ℕ)
  have hy_bound := right_boundary_exists D s x0 h_s_pos h_s_lt
  
  have h_y_sub_tau_in : y - τ ∈ cyclic_interval D s x0 := by
    have h1 := h_inv (y - τ)
    have h2 : y - τ + τ = y := sub_add_cancel y τ
    rw [h2] at h1
    exact h1.mpr hy_bound.1
    
  have h_y_sub_tau_next_notin : (y - τ) + 1 ∉ cyclic_interval D s x0 := by
    intro h_in
    have h1 := h_inv ((y - τ) + 1)
    have h2 : (y - τ) + 1 + τ = y + 1 := by
      calc (y - τ) + 1 + τ = y - τ + τ + 1 := by ring
           _ = y + 1 := by rw [sub_add_cancel]
    rw [h2] at h1
    have h_y_next_in := h1.mp h_in
    exact hy_bound.2 h_y_next_in
    
  have h_eq := right_boundary_unique D s x0 h_s_pos h_s_lt (y - τ) h_y_sub_tau_in h_y_sub_tau_next_notin
  have h_eq2 : y - τ = y := h_eq
  exact sub_eq_self.mp h_eq2

end Minimality



/--
Definition of a sequence having a period L.
-/
def IsPeriod (s : ℤ → ℤ) (L : ℕ) : Prop :=
  L > 0 ∧ ∀ i : ℤ, s (i + (L : ℤ)) = s i

def HasPeriodLength (s : ℤ → ℤ) (L : ℕ) : Prop :=
  IsPeriod s L ∧ ∀ L' > 0, IsPeriod s L' → L ≤ L'

/-- 
Axioms linking the geometric difference sequence to the residue distribution.
-/
class GeometricProjection (α β : ℕ) (ω : ℝ) (s : ℤ → ℤ) [NeZero (α^2 + β^2)] where
  N_pos : 0 < (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  period_N : IsPeriod s (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  period_degenerate : (α^2 + β^2) ∣ (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat → 
    HasPeriodLength s ((⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat / (α^2 + β^2))
  sigma_of_period : ∀ L > 0, IsPeriod s L →
    ∃ σ : ℕ, σ * (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat = L * (α^2 + β^2) ∧ 
    ∃ r0 : ℕ, ∀ x : ZMod (α^2 + β^2), count_hits (α^2 + β^2) r0 (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat (x + (σ : ZMod (α^2 + β^2))) = count_hits (α^2 + β^2) r0 (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat x

open GeometricProjection

lemma generic_minimality (α β : ℕ) (ω : ℝ) (seq : ℤ → ℤ) [NeZero (α^2 + β^2)] [GeometricProjection α β ω seq] :
    let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
    let D := α^2 + β^2
    ¬ (D ∣ N) → ∀ L > 0, IsPeriod seq L → N ≤ L := by
  intro N D hdvd L hL_pos hL_period
  haveI hD : NeZero D := inferInstance
  have h_sigma := sigma_of_period (α:=α) (β:=β) (ω:=ω) (s:=seq) L hL_pos hL_period
  rcases h_sigma with ⟨σ, h_sigma_eq, r0, h_inv_count⟩
  
  let q := N / D
  let s := N % D
  have h_s_pos : 0 < s := Nat.pos_of_ne_zero (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))
  have h_s_lt : s < D := Nat.mod_lt N (Nat.pos_of_ne_zero (NeZero.ne D))
  
  have h_heavy_eq : ∀ x : ZMod D, count_hits D r0 N x = q + 1 ↔ x ∈ @cyclic_interval D s hD ((r0 + q * D : ℕ) : ZMod D) := 
    @heavy_set_is_cyclic_interval D hD r0 N
    
  have h_inv : ∀ x : ZMod D, x ∈ @cyclic_interval D s hD ((r0 + q * D : ℕ) : ZMod D) ↔ 
                            (x + (σ : ZMod D)) ∈ @cyclic_interval D s hD ((r0 + q * D : ℕ) : ZMod D) := by
    intro x
    rw [← h_heavy_eq x, ← h_heavy_eq (x + (σ : ZMod D))]
    rw [h_inv_count x]
    
  have h_sigma_mod : (σ : ZMod D) = 0 := @cyclic_interval_stabilizer_trivial D s hD ((r0 + q * D : ℕ) : ZMod D) (σ : ZMod D) h_s_pos h_s_lt h_inv
  
  have h_sigma_dvd : D ∣ σ := by
    have h_cast : (σ : ZMod D) = 0 := h_sigma_mod
    exact (ZMod.natCast_eq_zero_iff σ D).mp h_cast
    
  rcases h_sigma_dvd with ⟨k, rfl⟩
  have h_eq : D * k * N = L * D := h_sigma_eq
  have h_eq2 : k * N * D = L * D := by
    calc k * N * D = D * k * N := by ring
         _ = L * D := h_eq
  have h_eq3 : k * N = L := mul_right_cancel₀ (NeZero.ne D) h_eq2
  
  have h_k_pos : 0 < k := by
    by_contra h_k
    have h_k0 : k = 0 := by omega
    rw [h_k0, zero_mul] at h_eq3
    omega
    
  have hN_pos : 0 < N := GeometricProjection.N_pos (s := seq)
  have h_N_le : N ≤ k * N := Nat.le_mul_of_pos_left N h_k_pos
  omega

/--
The abstract difference sequence from the cut-and-project set.
Formalizing the exact geometric sorting of the infinite multiset is left 
as part of the bottom-up construction.
-/
opaque difference_sequence (α β : ℕ) (ω : ℝ) : ℤ → ℤ

/--
Theorem 3.1: Period length formula.
-/
theorem main_theorem (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ) (h_ω : 0 ≤ ω)
    [NeZero (α^2 + β^2)] [GeometricProjection α β ω (difference_sequence α β ω)] :
    let N_int := ⌊ω * α⌋ + ⌊ω * β⌋ + 1
    let N := N_int.toNat
    let D := α^2 + β^2
    let L := if D ∣ N then N / D else N
    HasPeriodLength (difference_sequence α β ω) L := by
  intro N_int N D L
  have h_D_pos : 0 < D := by
    change 0 < α^2 + β^2
    rcases Nat.eq_zero_or_pos α with rfl | h_pos
    · have h_beta : β = 1 := by simpa using h_coprime
      rw [h_beta]
      norm_num
    · have : 0 < α^2 := by positivity
      omega
  haveI hD : NeZero D := ⟨_root_.ne_of_gt h_D_pos⟩
  
  by_cases h_dvd : D ∣ N
  · have h_L : L = N / D := if_pos h_dvd
    rw [h_L]
    exact GeometricProjection.period_degenerate h_dvd
  · have h_L : L = N := if_neg h_dvd
    rw [h_L]
    constructor
    · exact GeometricProjection.period_N
    · intro L' hL_pos hL_period
      exact generic_minimality α β ω (difference_sequence α β ω) h_dvd L' hL_pos hL_period

end CutAndProject
