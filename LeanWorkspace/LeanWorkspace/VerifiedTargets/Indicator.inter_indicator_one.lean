import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroOneClass M₀] {s t : Set ι} {i : ι}

theorem inter_indicator_one : (s ∩ t).indicator (1 : ι → M₀) = s.indicator 1 * t.indicator 1 := funext fun _ ↦ by simp only [← Set.inter_indicator_mul, Pi.mul_apply, Pi.one_apply, one_mul]; congr

