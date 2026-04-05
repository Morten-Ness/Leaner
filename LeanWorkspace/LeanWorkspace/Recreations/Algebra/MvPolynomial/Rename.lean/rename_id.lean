import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_id : MvPolynomial.rename id = AlgHom.id R (MvPolynomial σ R) := AlgHom.ext fun p ↦ eval₂_eta p

