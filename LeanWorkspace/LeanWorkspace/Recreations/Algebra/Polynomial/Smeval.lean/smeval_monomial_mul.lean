import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

variable [SMulCommClass R S S]

theorem smeval_monomial_mul (n : ℕ) :
    (monomial n r * p).smeval x = r • (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs =>
    simp only [Polynomial.smeval_add]
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, Polynomial.smeval_C_mul, Polynomial.smeval_X_pow_mul, Polynomial.smeval_add]
  | monomial n a =>
    rw [Polynomial.smeval_monomial, monomial_mul_monomial, Polynomial.smeval_monomial, npow_add, mul_smul, mul_smul_comm]

