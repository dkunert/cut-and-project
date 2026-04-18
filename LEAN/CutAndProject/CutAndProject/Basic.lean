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

end CutAndProject
