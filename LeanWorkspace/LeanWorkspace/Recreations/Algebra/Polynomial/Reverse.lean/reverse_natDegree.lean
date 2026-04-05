import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reverse_natDegree (f : R[X]) : f.reverse.natDegree = f.natDegree - f.natTrailingDegree := by
  rw [Polynomial.natDegree_eq_reverse_natDegree_add_natTrailingDegree f, add_tsub_cancel_right]

