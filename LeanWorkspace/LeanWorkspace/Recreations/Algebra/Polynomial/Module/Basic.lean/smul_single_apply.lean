import Mathlib

open scoped Polynomial

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

set_option backward.isDefEq.respectTransparency false in
theorem smul_single_apply (i : ℕ) (f : R[X]) (m : M) (n : ℕ) :
    (f • PolynomialModule.single R i m) n = ite (i ≤ n) (f.coeff (n - i) • m) 0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_smul, Finsupp.add_apply, hp, hq, coeff_add, add_smul]
    split_ifs
    exacts [rfl, zero_add 0]
  | monomial => grind [PolynomialModule.monomial_smul_single, PolynomialModule.single_apply, coeff_monomial, zero_smul]

