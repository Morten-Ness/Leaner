import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroClass M₀] {s t : Set ι} {i : ι}

theorem indicator_const_mul (s : Set ι) (f : ι → M₀) (a : M₀) (i : ι) :
    s.indicator (a * f ·) i = a * s.indicator f i := by rw [Set.indicator_mul_right]

