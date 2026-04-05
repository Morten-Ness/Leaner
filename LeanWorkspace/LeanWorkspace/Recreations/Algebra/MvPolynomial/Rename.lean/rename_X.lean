import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_X (f : σ → τ) (i : σ) : MvPolynomial.rename f (X i : MvPolynomial σ R) = X (f i) := eval₂_X _ _ _

