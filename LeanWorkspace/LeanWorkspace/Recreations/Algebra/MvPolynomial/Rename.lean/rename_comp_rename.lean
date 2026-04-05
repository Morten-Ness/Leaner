import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_comp_rename (f : σ → τ) (g : τ → α) :
    (MvPolynomial.rename (R := R) g).comp (MvPolynomial.rename f) = MvPolynomial.rename (g ∘ f) :=
  AlgHom.ext fun p ↦ MvPolynomial.rename_rename f g p

