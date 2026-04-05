import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

theorem natDegree_X_pow_le {R : Type*} [Semiring R] (n : ℕ) : (Polynomial.X ^ n : R[X]).natDegree ≤ n := by
  nontriviality R
  rw [Polynomial.natDegree_X_pow]

