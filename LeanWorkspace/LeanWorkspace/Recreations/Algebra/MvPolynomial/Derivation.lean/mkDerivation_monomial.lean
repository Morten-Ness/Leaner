import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

variable [IsScalarTower R (MvPolynomial σ R) A]

theorem mkDerivation_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    MvPolynomial.mkDerivation R f (monomial s r) =
      r • s.sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i := MvPolynomial.mkDerivationₗ_monomial f s r

