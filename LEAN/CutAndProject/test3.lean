import CutAndProject.Basic
import Mathlib

open Nat CutAndProject

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
  have h_sigma := sigma_of_period (α:=α) (β:=β) (ω:=ω) (s:=seq) L hL_pos hL_period
  rcases h_sigma with ⟨σ, h_sigma_eq, r0, h_inv_count⟩
  
  let q := N / D
  let s := N % D
  have h_s_pos : 0 < s := Nat.pos_of_ne_zero (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))
  have h_s_lt : s < D := Nat.mod_lt N (NeZero.pos D)
  
  have h_heavy_eq : ∀ x : ZMod D, count_hits D r0 N x = q + 1 ↔ x ∈ cyclic_interval D s ((r0 + q * D : ℕ) : ZMod D) := 
    heavy_set_is_cyclic_interval D r0 N
    
  have h_inv : ∀ x : ZMod D, x ∈ cyclic_interval D s ((r0 + q * D : ℕ) : ZMod D) ↔ 
                            (x + (σ : ZMod D)) ∈ cyclic_interval D s ((r0 + q * D : ℕ) : ZMod D) := by
    intro x
    rw [← h_heavy_eq x, ← h_heavy_eq (x + (σ : ZMod D))]
    rw [h_inv_count x]
    
  have h_sigma_mod : (σ : ZMod D) = 0 := cyclic_interval_stabilizer_trivial D s ((r0 + q * D : ℕ) : ZMod D) (σ : ZMod D) h_s_pos h_s_lt h_inv
  
  have h_sigma_dvd : D ∣ σ := by
    have h_cast : (σ : ZMod D) = 0 := h_sigma_mod
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd σ D).mp h_cast
    
  rcases h_sigma_dvd with ⟨k, rfl⟩
  have h_eq : k * D * N = L * D := h_sigma_eq
  have h_eq2 : k * N * D = L * D := by
    calc k * N * D = k * D * N := by ring
         _ = L * D := h_eq
  have h_eq3 : k * N = L := mul_right_cancel₀ (NeZero.ne D) h_eq2
  
  have h_k_pos : 0 < k := by
    by_contra h_k
    have h_k0 : k = 0 := by omega
    rw [h_k0, zero_mul] at h_eq3
    omega
    
  omega
