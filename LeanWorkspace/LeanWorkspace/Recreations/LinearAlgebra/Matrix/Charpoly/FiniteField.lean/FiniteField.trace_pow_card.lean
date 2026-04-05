import Mathlib

open scoped Polynomial

variable {n : Type*} [DecidableEq n] [Fintype n]

theorem FiniteField.trace_pow_card {K : Type*} [Field K] [Fintype K] (M : Matrix n n K) :
    Matrix.trace (M ^ Fintype.card K) = Matrix.trace M ^ Fintype.card K := by
  cases isEmpty_or_nonempty n
  · simp [Matrix.trace]
  rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
    FiniteField.Matrix.charpoly_pow_card, FiniteField.pow_card]

