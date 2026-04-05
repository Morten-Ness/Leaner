import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_add_le (p q : R[X]) : Polynomial.degree (p + q) ≤ max (Polynomial.degree p) (Polynomial.degree q) := by
  simpa only [Polynomial.degree, ← support_toFinsupp, toFinsupp_add]
    using AddMonoidAlgebra.sup_support_add_le _ _ _

