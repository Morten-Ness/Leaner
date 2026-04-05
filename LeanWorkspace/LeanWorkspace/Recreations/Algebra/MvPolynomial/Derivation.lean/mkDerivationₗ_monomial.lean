import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

theorem mkDerivationₗ_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    MvPolynomial.mkDerivationₗ R f (monomial s r) =
      r • s.sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i := sum_monomial_eq <| map_zero _

