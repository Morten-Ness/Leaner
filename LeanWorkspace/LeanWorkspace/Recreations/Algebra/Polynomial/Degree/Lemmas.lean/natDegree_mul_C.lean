import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]} {a : R}

variable [NoZeroDivisors R]

theorem natDegree_mul_C (a0 : a ≠ 0) : (p * Polynomial.C a).natDegree = p.natDegree := by
  simp only [natDegree, Polynomial.degree_mul_C a0]

