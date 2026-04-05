import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem support_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} [DecidableEq τ]
    (h : Function.Injective f) :
    (MvPolynomial.rename f p).support = Finset.image (Finsupp.mapDomain f) p.support := by
  rw [MvPolynomial.rename_eq]
  exact Finsupp.mapDomain_support_of_injective (Finsupp.mapDomain_injective h) _

