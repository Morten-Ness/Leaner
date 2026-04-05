import Mathlib

variable {R S : Type*}

variable [Semiring R] [AddCommMonoid S] [SMulWithZero R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

theorem smeval_single (n : ℤ) (r : R) : LaurentPolynomial.smeval (.single n r) x = r • (x ^ n).val := by
  simp only [LaurentPolynomial.smeval_eq_sum]
  rw [Finsupp.sum_single_index (zero_smul R (x ^ n).val)]

