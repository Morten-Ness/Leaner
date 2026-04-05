import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reverse_natDegree_le (f : R[X]) : f.reverse.natDegree ≤ f.natDegree := by
  rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
  intro n hn
  rw [Nat.cast_lt] at hn
  rw [Polynomial.coeff_reverse, Polynomial.revAt, Function.Embedding.coeFn_mk, if_neg (not_le_of_gt hn),
    coeff_eq_zero_of_natDegree_lt hn]

