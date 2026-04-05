import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_one' : Polynomial.hasseDeriv 1 f = derivative f := by
  simp only [Polynomial.hasseDeriv_apply, derivative_apply, ← C_mul_X_pow_eq_monomial, Nat.choose_one_right,
    (Nat.cast_commute _ _).eq]

