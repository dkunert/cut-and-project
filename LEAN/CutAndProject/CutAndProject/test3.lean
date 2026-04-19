import Mathlib
import CutAndProject.Basic

open Classical

namespace CutAndProject

noncomputable def sorted_multiset_test (α β : ℕ) (ω : ℝ) [NeZero (α^2 + β^2)] (i : ℤ) : ℤ :=
  let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
  let D := α^2 + β^2
  let r := (i % (N : ℤ)).toNat
  let q := i / (N : ℤ)
  (V α β ω r : ℤ) + q * D

noncomputable def diff_seq_test (α β : ℕ) (ω : ℝ) [NeZero (α^2 + β^2)] (i : ℤ) : ℤ :=
  sorted_multiset_test α β ω (i + 1) - sorted_multiset_test α β ω i

lemma period_N_test (α β : ℕ) (ω : ℝ) (h_ω : 0 ≤ ω) [NeZero (α^2 + β^2)] :
    let N := (⌊ω * α⌋ + ⌊ω * β⌋ + 1).toNat
    IsPeriod (diff_seq_test α β ω) N := by
  intro N
  unfold IsPeriod
  constructor
  · sorry
  · intro i
    dsimp [diff_seq_test, sorted_multiset_test]
    have hN_ne : (N : ℤ) ≠ 0 := sorry
    have h_mod1 : (i + (N : ℤ) + 1) % (N : ℤ) = (i + 1) % (N : ℤ) := by
      have h_eq : i + (N : ℤ) + 1 = i + 1 + (N : ℤ) := by omega
      rw [h_eq]
      have hm1 : (i + 1 + (N : ℤ)) % (N : ℤ) = ((i + 1) % (N : ℤ) + (N : ℤ) % (N : ℤ)) % (N : ℤ) := Int.add_emod (i + 1) (N : ℤ) (N : ℤ)
      have hm2 : (N : ℤ) % (N : ℤ) = 0 := Int.emod_self
      have hm3 : ((i + 1) % (N : ℤ)) % (N : ℤ) = (i + 1) % (N : ℤ) := Int.emod_emod (i + 1) (N : ℤ)
      rw [hm2, add_zero, hm3] at hm1
      exact hm1
    have h_mod2 : (i + (N : ℤ)) % (N : ℤ) = i % (N : ℤ) := by
      have hm1 : (i + (N : ℤ)) % (N : ℤ) = (i % (N : ℤ) + (N : ℤ) % (N : ℤ)) % (N : ℤ) := Int.add_emod i (N : ℤ) (N : ℤ)
      have hm2 : (N : ℤ) % (N : ℤ) = 0 := Int.emod_self
      have hm3 : (i % (N : ℤ)) % (N : ℤ) = i % (N : ℤ) := Int.emod_emod i (N : ℤ)
      rw [hm2, add_zero, hm3] at hm1
      exact hm1
    have h_div1 : (i + (N : ℤ) + 1) / (N : ℤ) = (i + 1) / (N : ℤ) + 1 := by
      have h_eq : i + (N : ℤ) + 1 = i + 1 + (N : ℤ) := by omega
      rw [h_eq]
      have hd1 : (i + 1 + (N : ℤ)) / (N : ℤ) = (i + 1) / (N : ℤ) + (N : ℤ) / (N : ℤ) := Int.add_ediv_of_dvd_right (dvd_refl (N : ℤ))
      have hd2 : (N : ℤ) / (N : ℤ) = 1 := Int.ediv_self hN_ne
      rw [hd2] at hd1
      exact hd1
    have h_div2 : (i + (N : ℤ)) / (N : ℤ) = i / (N : ℤ) + 1 := by
      have hd1 : (i + (N : ℤ)) / (N : ℤ) = i / (N : ℤ) + (N : ℤ) / (N : ℤ) := Int.add_ediv_of_dvd_right (dvd_refl (N : ℤ))
      have hd2 : (N : ℤ) / (N : ℤ) = 1 := Int.ediv_self hN_ne
      rw [hd2] at hd1
      exact hd1
    rw [h_mod1, h_mod2, h_div1, h_div2]
    ring

end CutAndProject
