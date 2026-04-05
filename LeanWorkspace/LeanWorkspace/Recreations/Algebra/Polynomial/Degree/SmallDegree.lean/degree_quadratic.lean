import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_quadratic (ha : a ≠ 0) : degree (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) = 2 := by
  rw [add_assoc, degree_add_eq_left_of_degree_lt <| Polynomial.degree_linear_lt_degree_C_mul_X_sq ha,
    degree_C_mul_X_pow 2 ha]
  rfl

