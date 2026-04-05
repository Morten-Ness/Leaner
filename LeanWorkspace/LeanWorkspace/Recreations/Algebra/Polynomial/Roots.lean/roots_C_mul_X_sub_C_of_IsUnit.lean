import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_C_mul_X_sub_C_of_IsUnit (b : R) (a : Rˣ) : (C (a : R) * X - C b).roots =
    {a⁻¹ * b} := by
  rw [← Polynomial.roots_C_mul _ (Units.ne_zero a⁻¹), mul_sub, ← mul_assoc, ← C_mul, ← C_mul,
    Units.inv_mul, C_1, one_mul]
  exact Polynomial.roots_X_sub_C (a⁻¹ * b)

