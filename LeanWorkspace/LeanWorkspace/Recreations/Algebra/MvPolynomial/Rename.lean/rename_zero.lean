import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_zero (f : σ → τ) : (0 : MvPolynomial σ R).rename f = 0 := rfl

