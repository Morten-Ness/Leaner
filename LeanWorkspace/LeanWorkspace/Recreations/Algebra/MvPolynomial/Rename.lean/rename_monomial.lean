import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_monomial (f : σ → τ) (d : σ →₀ ℕ) (r : R) :
    MvPolynomial.rename f (monomial d r) = monomial (d.mapDomain f) r := by
  rw [MvPolynomial.rename, aeval_monomial, monomial_eq (s := Finsupp.mapDomain f d),
    Finsupp.prod_mapDomain_index, algebraMap_eq]
  · simp_rw [Function.comp_apply]
  · exact fun n => pow_zero _
  · exact fun n i₁ i₂ => pow_add _ _ _

