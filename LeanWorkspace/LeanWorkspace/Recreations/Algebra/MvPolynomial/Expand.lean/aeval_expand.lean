import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem aeval_expand {A : Type*} [CommSemiring A] [Algebra R A]
    (f : σ → A) (φ : MvPolynomial σ R) :
    aeval f (MvPolynomial.expand p φ) = aeval (f ^ p) φ := MvPolynomial.eval₂_expand ..

