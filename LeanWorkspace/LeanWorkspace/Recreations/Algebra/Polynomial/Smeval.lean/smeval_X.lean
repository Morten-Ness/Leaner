import Mathlib

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

theorem smeval_X :
    (X : R[X]).smeval x = x ^ 1 := by
  simp only [Polynomial.smeval_eq_sum, Polynomial.smul_pow, zero_smul, sum_X_index, one_smul]

