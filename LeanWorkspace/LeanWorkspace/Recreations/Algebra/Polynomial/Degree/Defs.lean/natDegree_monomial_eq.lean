import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_monomial_eq (i : ℕ) {r : R} (r0 : r ≠ 0) : (monomial i r).natDegree = i := letI := Classical.decEq R
  Eq.trans (Polynomial.natDegree_monomial _ _) (if_neg r0)

