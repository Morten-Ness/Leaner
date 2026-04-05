import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem natDegree_sub_C {a : R} : natDegree (p - Polynomial.C a) = natDegree p := by
  rw [sub_eq_add_neg, ← C_neg, natDegree_add_C]

