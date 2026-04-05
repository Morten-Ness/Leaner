import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem C_mul_X_pow_eq_self (h : #p.support ≤ 1) : Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree = p := by
  rw [C_mul_X_pow_eq_monomial, Polynomial.monomial_natDegree_leadingCoeff_eq_self h]

