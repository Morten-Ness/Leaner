import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

theorem smeval_at_zero : p.smeval (0 : S) = (p.coeff 0) • (1 : S) := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp_all only [Polynomial.smeval_add, coeff_add, add_smul]
  | monomial n a =>
    cases n with
    | zero => simp only [monomial_zero_left, Polynomial.smeval_C, npow_zero, coeff_C_zero]
    | succ n => rw [coeff_monomial_succ, Polynomial.smeval_monomial, npow_add, npow_one, mul_zero, zero_smul,
        smul_zero]

