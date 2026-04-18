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

/--
Lemma 4.3: Non-uniform residue distribution.
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
  sorry

/--
Definition of a sequence having a period L.
-/
def IsPeriod (s : ℤ → ℤ) (L : ℕ) : Prop :=
  L > 0 ∧ ∀ i : ℤ, s (i + (L : ℤ)) = s i

def HasPeriodLength (s : ℤ → ℤ) (L : ℕ) : Prop :=
  IsPeriod s L ∧ ∀ L' > 0, IsPeriod s L' → L ≤ L'

/--
The abstract difference sequence from the cut-and-project set.
Formalizing the exact geometric sorting of the infinite multiset is left 
as part of the bottom-up construction.
-/
opaque difference_sequence (α β : ℕ) (ω : ℝ) : ℤ → ℤ

/--
Theorem 3.1: Period length formula.
-/
theorem main_theorem (α β : ℕ) (h_coprime : Nat.Coprime α β) (ω : ℝ) (h_ω : 0 ≤ ω) :
    let N_int := ⌊ω * α⌋ + ⌊ω * β⌋ + 1
    let N := N_int.toNat
    let D := α^2 + β^2
    let L := if D ∣ N then N / D else N
    HasPeriodLength (difference_sequence α β ω) L := by
  sorry

end CutAndProject
