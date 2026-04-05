import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_linear (ha : a ≠ 0) : degree (Polynomial.C a * Polynomial.X + Polynomial.C b) = 1 := by
  rw [degree_add_eq_left_of_degree_lt <| degree_C_lt_degree_C_mul_X ha, degree_C_mul_X ha]

