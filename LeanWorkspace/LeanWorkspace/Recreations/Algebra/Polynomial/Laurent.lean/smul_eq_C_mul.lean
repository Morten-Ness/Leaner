import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
theorem smul_eq_C_mul (r : R) (f : R[T;T⁻¹]) : r • f = Polynomial.C r * f := by
  induction f using LaurentPolynomial.induction_on' with
  | add _ _ hp hq =>
    rw [smul_add, mul_add, hp, hq]
  | C_mul_T n s =>
    rw [← mul_assoc, ← smul_mul_assoc, mul_left_inj_of_invertible, ← map_mul, ← LaurentPolynomial.single_eq_C,
      Finsupp.smul_single']
    rfl

