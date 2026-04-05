import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R] [AddCommMonoid S] [SMulWithZero R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

set_option backward.isDefEq.respectTransparency false in
theorem smeval_zero : (0 : R[T;T⁻¹]).smeval x = (0 : S) := by
  simp only [LaurentPolynomial.smeval_eq_sum, Finsupp.sum_zero_index]

