import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]} {a : R}

variable [NoZeroDivisors R]

theorem natDegree_C_mul (a0 : a ≠ 0) : (Polynomial.C a * p).natDegree = p.natDegree := by
  simp only [natDegree, Polynomial.degree_C_mul a0]

