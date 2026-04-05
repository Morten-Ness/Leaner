import Mathlib

open scoped Polynomial

theorem cardinalMk_le_max {R : Type u} [Semiring R] : #(R[X]) ≤ max #R ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph0)
  · exact Polynomial.cardinalMk_eq_max.le

