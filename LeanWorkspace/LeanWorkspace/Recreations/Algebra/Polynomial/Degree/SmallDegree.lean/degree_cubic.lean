import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_cubic (ha : a ≠ 0) : degree (Polynomial.C a * Polynomial.X ^ 3 + Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X + Polynomial.C d) = 3 := by
  rw [add_assoc, add_assoc, ← add_assoc (Polynomial.C b * Polynomial.X ^ 2),
    degree_add_eq_left_of_degree_lt <| Polynomial.degree_quadratic_lt_degree_C_mul_X_cb ha,
    degree_C_mul_X_pow 3 ha]
  rfl

