import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_cubic (ha : a ≠ 0) :
    leadingCoeff (Polynomial.C a * Polynomial.X ^ 3 + Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X + Polynomial.C d) = a := by
  rw [add_assoc, add_assoc, ← add_assoc (Polynomial.C b * Polynomial.X ^ 2), add_comm,
    Polynomial.leadingCoeff_add_of_degree_lt <| Polynomial.degree_quadratic_lt_degree_C_mul_X_cb ha,
    leadingCoeff_C_mul_X_pow]

