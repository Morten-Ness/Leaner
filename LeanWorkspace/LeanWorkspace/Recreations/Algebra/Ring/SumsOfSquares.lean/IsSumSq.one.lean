import Mathlib

variable {R : Type*}

theorem IsSumSq.one [AddZeroClass R] [MulOneClass R] : IsSumSq (1 : R) := by aesop

