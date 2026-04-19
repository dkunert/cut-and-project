import Mathlib

lemma test_div (i N : ℤ) (h : 0 < N) : (i + N) / N = i / N + 1 := by
  omega

lemma test_mod (i N : ℤ) (h : 0 < N) : (i + N) % N = i % N := by
  omega
