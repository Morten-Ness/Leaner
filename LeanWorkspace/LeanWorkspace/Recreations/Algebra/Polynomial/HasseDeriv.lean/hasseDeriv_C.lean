import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_C (r : R) (hk : 0 < k) : Polynomial.hasseDeriv k (Polynomial.C r) = 0 := by
  rw [← monomial_zero_left, Polynomial.hasseDeriv_monomial, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero,
    zero_mul, monomial_zero_right]

