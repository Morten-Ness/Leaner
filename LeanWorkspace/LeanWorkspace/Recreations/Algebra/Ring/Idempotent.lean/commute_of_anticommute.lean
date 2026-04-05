import Mathlib

variable {R : Type*}

theorem commute_of_anticommute {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
    (ha : IsIdempotentElem a) (hab : a * b + b * a = 0) : Commute a b := by
  have := IsIdempotentElem.mul_eq_zero_of_anticommute ha hab
  rw [this, zero_add] at hab
  rw [Commute, SemiconjBy, hab, this]

