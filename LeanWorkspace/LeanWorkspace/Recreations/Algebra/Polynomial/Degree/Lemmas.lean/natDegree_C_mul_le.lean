import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_C_mul_le (a : R) (f : R[X]) : (Polynomial.C a * f).natDegree ≤ f.natDegree := by
  simpa using natDegree_mul_le (p := Polynomial.C a)

