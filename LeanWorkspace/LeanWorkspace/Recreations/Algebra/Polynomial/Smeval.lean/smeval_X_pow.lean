import Mathlib

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

theorem smeval_X_pow {n : ℕ} :
    (X ^ n : R[X]).smeval x = x ^ n := by
  simp only [Polynomial.smeval_eq_sum, Polynomial.smul_pow, X_pow_eq_monomial, zero_smul, sum_monomial_index, one_smul]

