import Mathlib

variable {R S : Type*}

variable [Semiring R] [AddCommMonoid S] [SMulWithZero R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

theorem smeval_C_mul_T_n (n : ℤ) (r : R) : (Polynomial.C r * LaurentPolynomial.T n).smeval x = r • (x ^ n).val := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.smeval_single]

