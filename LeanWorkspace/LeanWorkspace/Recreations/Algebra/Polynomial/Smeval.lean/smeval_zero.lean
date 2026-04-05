import Mathlib

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

theorem smeval_zero : (0 : R[X]).smeval x = 0 := by
  simp only [Polynomial.smeval_eq_sum, sum_zero_index]

