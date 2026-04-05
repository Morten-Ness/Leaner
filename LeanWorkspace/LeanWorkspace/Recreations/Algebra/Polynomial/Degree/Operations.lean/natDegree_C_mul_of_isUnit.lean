import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (Polynomial.C a * p).natDegree = p.natDegree := by
  simp [natDegree, Polynomial.degree_C_mul_of_isUnit ha]

