import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroOneClass M₀] {s t : Set ι} {i : ι}

theorem inter_indicator_one : (s ∩ t).indicator (1 : ι → M₀) = s.indicator 1 * t.indicator 1 := by
  ext i
  by_cases hs : i ∈ s
  · by_cases ht : i ∈ t
    · simp [Set.indicator, hs, ht]
    · simp [Set.indicator, hs, ht]
  · simp [Set.indicator, hs]
