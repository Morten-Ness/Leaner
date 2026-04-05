import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_C_mul_X_add_C_of_IsUnit (b : R) (a : Rˣ) : (C (a : R) * X + C b).roots =
    {-(a⁻¹ * b)} := by
  rw [← sub_neg_eq_add, ← C_neg, Polynomial.roots_C_mul_X_sub_C_of_IsUnit, mul_neg]

