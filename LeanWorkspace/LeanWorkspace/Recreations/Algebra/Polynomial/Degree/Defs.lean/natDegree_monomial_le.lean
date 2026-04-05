import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_monomial_le (a : R) {m : ℕ} : (monomial m a).natDegree ≤ m := by
  classical
  rw [Polynomial.natDegree_monomial]
  split_ifs
  exacts [Nat.zero_le _, le_rfl]

