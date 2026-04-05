import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

variable [IsScalarTower R S S]

variable [SMulCommClass R S S]

theorem smeval_comp : (p.comp q).smeval x = p.smeval (q.smeval x) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp [add_comp, hr, hs, Polynomial.smeval_add]
  | monomial n a => simp [Polynomial.smeval_monomial, Polynomial.smeval_C_mul, Polynomial.smeval_pow]

