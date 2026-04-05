import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem eval_expand (f : σ → R) (φ : MvPolynomial σ R) :
    eval f (MvPolynomial.expand p φ) = eval (f ^ p) φ := MvPolynomial.eval₂_expand ..

