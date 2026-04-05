import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_X (i : σ) : MvPolynomial.expand p (X i : MvPolynomial σ R) = X i ^ p := eval₂Hom_X' _ _ _

