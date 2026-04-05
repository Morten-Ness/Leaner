import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

theorem mkDerivationₗ_X (f : σ → A) (i : σ) : MvPolynomial.mkDerivationₗ R f (X i) = f i := (MvPolynomial.mkDerivationₗ_monomial f _ _).trans <| by simp [tsub_self]

