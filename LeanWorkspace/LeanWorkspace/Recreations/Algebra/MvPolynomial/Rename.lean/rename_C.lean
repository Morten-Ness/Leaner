import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_C (f : σ → τ) (r : R) : MvPolynomial.rename f (C r) = C r := eval₂_C _ _ _

