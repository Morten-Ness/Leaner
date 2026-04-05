import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroClass M₀] {s t : Set ι} {i : ι}

theorem indicator_mul_const (s : Set ι) (f : ι → M₀) (a : M₀) (i : ι) :
    s.indicator (f · * a) i = s.indicator f i * a := by rw [Set.indicator_mul_left]

