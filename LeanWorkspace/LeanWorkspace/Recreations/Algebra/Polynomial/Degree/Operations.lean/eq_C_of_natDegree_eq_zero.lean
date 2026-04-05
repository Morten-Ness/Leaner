import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem eq_C_of_natDegree_eq_zero (h : natDegree p = 0) : p = Polynomial.C (coeff p 0) := Polynomial.eq_C_of_natDegree_le_zero h.le

