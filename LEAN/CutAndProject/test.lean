import CutAndProject.Basic
import Mathlib

open Nat

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
