import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_natDegree_le (f : R[X]) : (Polynomial.eraseLead f).natDegree ≤ f.natDegree - 1 := by
  rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero f with (h | h)
  · exact Nat.le_sub_one_of_lt h
  · simp only [h, natDegree_zero, zero_le]

