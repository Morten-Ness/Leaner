import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_X (hk : 1 < k) : Polynomial.hasseDeriv k (Polynomial.X : R[X]) = 0 := by
  rw [← monomial_one_one_eq_X, Polynomial.hasseDeriv_monomial, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero,
    zero_mul, monomial_zero_right]

