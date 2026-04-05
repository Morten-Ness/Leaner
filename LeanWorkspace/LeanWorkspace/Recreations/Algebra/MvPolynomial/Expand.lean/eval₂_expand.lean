import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem eval₂_expand (f : R →+* S) (g : σ → S) (φ : MvPolynomial σ R) :
    eval₂ f g (MvPolynomial.expand p φ) = eval₂ f (g ^ p) φ := DFunLike.congr_fun (MvPolynomial.eval₂Hom_comp_expand p f g) φ

