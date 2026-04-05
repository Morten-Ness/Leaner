import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]}

theorem eq_X_pow_iff_natTrailingDegree_eq_natDegree (h₁ : p.Monic) :
    p = Polynomial.X ^ p.natDegree ↔ p.natTrailingDegree = p.natDegree := Polynomial.Monic.eq_X_pow_iff_natDegree_le_natTrailingDegree h₁.trans (Polynomial.natTrailingDegree_le_natDegree p).ge_iff_eq

