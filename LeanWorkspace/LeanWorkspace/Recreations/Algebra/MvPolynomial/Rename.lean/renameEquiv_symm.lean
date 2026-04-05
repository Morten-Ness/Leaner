import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem renameEquiv_symm (f : σ ≃ τ) : (MvPolynomial.renameEquiv R f).symm = MvPolynomial.renameEquiv R f.symm := rfl

