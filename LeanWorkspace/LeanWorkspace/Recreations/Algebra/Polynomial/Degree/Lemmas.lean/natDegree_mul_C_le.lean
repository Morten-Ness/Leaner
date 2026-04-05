import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_mul_C_le (f : R[X]) (a : R) : (f * Polynomial.C a).natDegree ≤ f.natDegree := by
  simpa using natDegree_mul_le (q := Polynomial.C a)

