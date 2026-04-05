import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroClass M₀] {s t : Set ι} {i : ι}

theorem inter_indicator_mul (f g : ι → M₀) (i : ι) :
    (s ∩ t).indicator (fun j ↦ f j * g j) i = s.indicator f i * t.indicator g i := by
  rw [← Set.indicator_indicator]
  simp_rw [indicator]
  split_ifs <;> simp

