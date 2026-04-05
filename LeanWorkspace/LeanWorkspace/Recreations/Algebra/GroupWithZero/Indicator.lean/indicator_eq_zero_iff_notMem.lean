import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroOneClass M₀] {s t : Set ι} {i : ι}

variable (M₀) [Nontrivial M₀]

theorem indicator_eq_zero_iff_notMem : indicator s 1 i = (0 : M₀) ↔ i ∉ s := by
  classical simp [indicator_apply, imp_false]

