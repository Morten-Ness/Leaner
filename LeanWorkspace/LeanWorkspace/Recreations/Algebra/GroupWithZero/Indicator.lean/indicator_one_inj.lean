import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroOneClass M₀] {s t : Set ι} {i : ι}

variable (M₀) [Nontrivial M₀]

theorem indicator_one_inj (h : indicator s (1 : ι → M₀) = indicator t 1) : s = t := by
  ext; simp_rw [← Set.indicator_eq_one_iff_mem M₀, h]

