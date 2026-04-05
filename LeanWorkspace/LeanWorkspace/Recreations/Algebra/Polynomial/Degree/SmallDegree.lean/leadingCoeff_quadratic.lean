import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_quadratic (ha : a ≠ 0) : leadingCoeff (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) = a := by
  rw [add_assoc, add_comm, Polynomial.leadingCoeff_add_of_degree_lt <| Polynomial.degree_linear_lt_degree_C_mul_X_sq ha,
    leadingCoeff_C_mul_X_pow]

