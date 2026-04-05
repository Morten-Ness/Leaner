import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem natDegree_pos_of_eraseLead_ne_zero (h : f.eraseLead ≠ 0) : 0 < f.natDegree := by
  by_contra h₂
  rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h₂)] at h
  simp at h

