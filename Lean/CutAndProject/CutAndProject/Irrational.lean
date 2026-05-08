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

end CutAndProject.Irrational
