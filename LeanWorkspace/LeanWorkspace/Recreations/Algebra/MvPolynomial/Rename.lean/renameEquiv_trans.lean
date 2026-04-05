import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ α) :
    (MvPolynomial.renameEquiv R e).trans (MvPolynomial.renameEquiv R f) = MvPolynomial.renameEquiv R (e.trans f) := AlgEquiv.ext (MvPolynomial.rename_rename e f)

