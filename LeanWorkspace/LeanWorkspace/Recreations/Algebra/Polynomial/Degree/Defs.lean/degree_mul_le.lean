import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_mul_le (p q : R[X]) : Polynomial.degree (p * q) ≤ Polynomial.degree p + Polynomial.degree q := by
  simpa [Polynomial.degree, ← support_toFinsupp] using AddMonoidAlgebra.sup_support_mul_le (by simp) ..

