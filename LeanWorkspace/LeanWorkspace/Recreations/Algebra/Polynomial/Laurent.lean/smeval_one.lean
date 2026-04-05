import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R] [AddCommMonoid S] [MulActionWithZero R S] [Monoid S] (f g : R[T;T⁻¹])
  (x y : Sˣ)

theorem smeval_one : (1 : R[T;T⁻¹]).smeval x = 1 := by
  rw [← LaurentPolynomial.T_zero, LaurentPolynomial.smeval_T_pow 0 x, zpow_zero, Units.val_eq_one]

