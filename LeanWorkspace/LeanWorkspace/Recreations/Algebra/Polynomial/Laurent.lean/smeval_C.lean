import Mathlib

variable {R S : Type*}

variable [Semiring R] [AddCommMonoid S] [SMulWithZero R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

theorem smeval_C (r : R) : (Polynomial.C r).smeval x = r • 1 := by
  rw [← LaurentPolynomial.single_eq_C, LaurentPolynomial.smeval_single x (0 : ℤ) r, zpow_zero, Units.val_one]

