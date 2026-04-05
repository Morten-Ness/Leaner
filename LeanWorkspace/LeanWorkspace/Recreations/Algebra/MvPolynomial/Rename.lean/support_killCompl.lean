import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

theorem support_killCompl {p : MvPolynomial τ R} :
    (p.killCompl hf).support =
      p.support.preimage (Finsupp.mapDomain f) (Finsupp.mapDomain_injective hf).injOn := by
  ext x
  simp [MvPolynomial.coeff_killCompl]

