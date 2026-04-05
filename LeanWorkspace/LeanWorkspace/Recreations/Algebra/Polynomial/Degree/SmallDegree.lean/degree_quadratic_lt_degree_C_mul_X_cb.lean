import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_quadratic_lt_degree_C_mul_X_cb (ha : a ≠ 0) :
    degree (Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X + Polynomial.C d) < degree (Polynomial.C a * Polynomial.X ^ 3) := by
  simpa only [degree_C_mul_X_pow 3 ha] using Polynomial.degree_quadratic_lt

