import Mathlib

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

theorem smeval_monomial (n : ℕ) :
    (monomial n r).smeval x = r • x ^ n := by
  simp only [Polynomial.smeval_eq_sum, Polynomial.smul_pow, zero_smul, sum_monomial_index]

