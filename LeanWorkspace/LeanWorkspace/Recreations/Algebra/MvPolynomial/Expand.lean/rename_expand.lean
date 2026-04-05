import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem rename_expand (f : σ → τ) (φ : MvPolynomial σ R) :
    rename f (MvPolynomial.expand p φ) = MvPolynomial.expand p (rename f φ) := DFunLike.congr_fun (MvPolynomial.rename_comp_expand p f) φ

