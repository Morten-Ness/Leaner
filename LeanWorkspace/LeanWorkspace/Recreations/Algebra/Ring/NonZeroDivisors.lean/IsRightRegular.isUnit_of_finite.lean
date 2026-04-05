import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Monoid R] {r : R}

variable [Finite R]

theorem IsRightRegular.isUnit_of_finite (h : IsRightRegular r) : IsUnit r := by
  rwa [IsUnit.isUnit_iff_mulRight_bijective, ← Finite.injective_iff_bijective]

