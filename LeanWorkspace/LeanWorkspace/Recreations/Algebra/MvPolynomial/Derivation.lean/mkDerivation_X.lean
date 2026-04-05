import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

variable [IsScalarTower R (MvPolynomial σ R) A]

theorem mkDerivation_X (f : σ → A) (i : σ) : MvPolynomial.mkDerivation R f (X i) = f i := MvPolynomial.mkDerivationₗ_X f i

