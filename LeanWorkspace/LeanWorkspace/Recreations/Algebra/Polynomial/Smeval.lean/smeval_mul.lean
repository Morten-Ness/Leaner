import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

variable [IsScalarTower R S S]

variable [SMulCommClass R S S]

theorem smeval_mul : (p * q).smeval x = p.smeval x * q.smeval x := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [hr, hs, Polynomial.smeval_add, add_mul]
  | monomial n a =>
    simp only [Polynomial.smeval_monomial, Polynomial.smeval_monomial_mul, smul_mul_assoc]

