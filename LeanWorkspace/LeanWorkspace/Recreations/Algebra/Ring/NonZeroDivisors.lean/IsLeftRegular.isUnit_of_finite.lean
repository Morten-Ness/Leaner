import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Monoid R] {r : R}

variable [Finite R]

theorem IsLeftRegular.isUnit_of_finite (h : IsLeftRegular r) : IsUnit r := by
  rwa [IsUnit.isUnit_iff_mulLeft_bijective, ← Finite.injective_iff_bijective]

