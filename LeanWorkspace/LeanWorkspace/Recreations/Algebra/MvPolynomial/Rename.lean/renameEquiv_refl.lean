import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem renameEquiv_refl : MvPolynomial.renameEquiv R (Equiv.refl σ) = AlgEquiv.refl := AlgEquiv.ext (by simp)

