import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_linear_lt_degree_C_mul_X_sq (ha : a ≠ 0) :
    degree (Polynomial.C b * Polynomial.X + Polynomial.C c) < degree (Polynomial.C a * Polynomial.X ^ 2) := by
  simpa only [degree_C_mul_X_pow 2 ha] using Polynomial.degree_linear_lt

