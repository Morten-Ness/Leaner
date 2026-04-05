import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem ne_zero (hp : p.IsUnitTrinomial) : p ≠ 0 := by
  rintro rfl
  simpa using Polynomial.IsUnitTrinomial.card_support_eq_three hp

