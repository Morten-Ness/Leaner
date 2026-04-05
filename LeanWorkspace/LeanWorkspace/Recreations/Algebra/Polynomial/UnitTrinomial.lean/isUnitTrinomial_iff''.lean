import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem isUnitTrinomial_iff'' (h : p * p.mirror = q * q.mirror) :
    p.IsUnitTrinomial ↔ q.IsUnitTrinomial := by
  rw [Polynomial.isUnitTrinomial_iff', Polynomial.isUnitTrinomial_iff', h]

