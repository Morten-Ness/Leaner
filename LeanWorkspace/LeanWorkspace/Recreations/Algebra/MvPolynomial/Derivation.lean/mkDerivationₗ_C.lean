import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

theorem mkDerivationₗ_C (f : σ → A) (r : R) : MvPolynomial.mkDerivationₗ R f (C r) = 0 := (MvPolynomial.mkDerivationₗ_monomial f _ _).trans (smul_zero _)

