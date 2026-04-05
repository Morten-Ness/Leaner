import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem withBotSucc_degree_eq_natDegree_add_one (h : p ≠ 0) : p.degree.succ = p.natDegree + 1 := by
  rw [Polynomial.degree_eq_natDegree h]
  exact WithBot.succ_coe p.natDegree

