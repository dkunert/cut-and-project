import Mathlib

open Nat

lemma D_pos (α β : ℕ) (h : Nat.Coprime α β) : 0 < α^2 + β^2 := by
  rcases Nat.eq_zero_or_pos α with rfl | hα
  · rw [Nat.coprime_zero_left] at h
    rw [h]
    decide
  · have h1 : 0 < α^2 := Nat.pos_of_ne_zero (pow_ne_zero 2 (Nat.ne_of_gt hα))
    omega

theorem coprime_beta_D (α β : ℕ) (h : Nat.Coprime α β) : Nat.Coprime β (α^2 + β^2) := by
  have h1 : Nat.Coprime β (α^2) := Nat.Coprime.pow_right 2 h.symm
  have h2 : α^2 + β^2 = α^2 + β * β := by ring
  rw [h2]
  exact (Nat.coprime_add_mul_right_right β (α^2) β).mpr h1

theorem coprime_alpha_D (α β : ℕ) (h : Nat.Coprime α β) : Nat.Coprime α (α^2 + β^2) := by
  have h1 : Nat.Coprime α (β^2) := Nat.Coprime.pow_right 2 h
  have h2 : α^2 + β^2 = β^2 + α * α := by ring
  rw [h2]
  exact (Nat.coprime_add_mul_right_right α (β^2) α).mpr h1

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
