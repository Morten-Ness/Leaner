import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_injective (f : σ → τ) (hf : Function.Injective f) :
    Function.Injective (MvPolynomial.rename f : MvPolynomial σ R → MvPolynomial τ R) := by
  have :
    (MvPolynomial.rename f : MvPolynomial σ R → MvPolynomial τ R) = Finsupp.mapDomain (Finsupp.mapDomain f) :=
    funext (MvPolynomial.rename_eq f)
  rw [this]
  exact Finsupp.mapDomain_injective (Finsupp.mapDomain_injective hf)

