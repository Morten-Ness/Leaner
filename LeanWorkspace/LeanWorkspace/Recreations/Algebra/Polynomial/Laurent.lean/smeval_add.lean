import Mathlib

variable {R S : Type*}

variable [Semiring R] [AddCommMonoid S] [Module R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

set_option backward.isDefEq.respectTransparency false in
theorem smeval_add : (f + g).smeval x = f.smeval x + g.smeval x := by
  simp only [LaurentPolynomial.smeval_eq_sum]
  rw [Finsupp.sum_add_index (fun n _ => zero_smul R (x ^ n).val) (fun n _ r r' => add_smul r r' _)]

