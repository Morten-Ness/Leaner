import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R] [AddCommMonoid S] [MulActionWithZero R S] [Monoid S] (f g : R[T;T⁻¹])
  (x y : Sˣ)

theorem smeval_T_pow (n : ℤ) (x : Sˣ) : (LaurentPolynomial.T n : R[T;T⁻¹]).smeval x = (x ^ n).val := by
  rw [LaurentPolynomial.T, LaurentPolynomial.smeval_single, one_smul]

