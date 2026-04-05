import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_zero' : Polynomial.hasseDeriv 0 f = f := by
  simp only [Polynomial.hasseDeriv_apply, Nat.sub_zero, choose_zero_right, cast_one, one_mul, sum_monomial_eq]

