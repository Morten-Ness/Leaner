import Mathlib

variable {R S : Type*}

variable [Semiring R] [AddCommMonoid S] [Module R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

theorem smeval_C_mul (r : R) : (Polynomial.C r * f).smeval x = r • (f.smeval x) := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add, LaurentPolynomial.smeval_add, LaurentPolynomial.smeval_add, smul_add, hp, hq]
  | C_mul_T n s =>
    rw [← mul_assoc, ← map_mul, LaurentPolynomial.smeval_C_mul_T_n, LaurentPolynomial.smeval_C_mul_T_n, mul_smul]

