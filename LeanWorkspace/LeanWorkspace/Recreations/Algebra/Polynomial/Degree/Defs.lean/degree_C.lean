import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_C (ha : a ≠ 0) : Polynomial.degree (Polynomial.C a) = (0 : WithBot ℕ) := by
  rw [Polynomial.degree, ← monomial_zero_left, support_monomial 0 ha, max_eq_sup_coe, sup_singleton,
    WithBot.coe_zero]

