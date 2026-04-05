import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_C_lt_degree_C_mul_X (ha : a ≠ 0) : degree (Polynomial.C b) < degree (Polynomial.C a * Polynomial.X) := by
  simpa only [degree_C_mul_X ha] using degree_C_lt

