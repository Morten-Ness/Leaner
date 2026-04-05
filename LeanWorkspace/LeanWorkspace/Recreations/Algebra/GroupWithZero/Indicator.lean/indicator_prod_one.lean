import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroOneClass M₀] {s t : Set ι} {i : ι}

theorem indicator_prod_one {t : Set κ} {j : κ} :
    (s ×ˢ t).indicator (1 : ι × κ → M₀) (i, j) = s.indicator 1 i * t.indicator 1 j := by
  simp_rw [indicator, mem_prod_eq]
  split_ifs with h₀ <;> simp only [Pi.one_apply, mul_one, mul_zero] <;> tauto

