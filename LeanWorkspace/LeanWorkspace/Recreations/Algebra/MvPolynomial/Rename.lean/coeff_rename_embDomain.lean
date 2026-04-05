import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem coeff_rename_embDomain (f : σ ↪ τ) (φ : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (MvPolynomial.rename f φ).coeff (d.embDomain f) = φ.coeff d := by
  rw [Finsupp.embDomain_eq_mapDomain f, MvPolynomial.coeff_rename_mapDomain f f.injective]

