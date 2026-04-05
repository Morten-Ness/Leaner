import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

theorem killCompl_monomial_mapDomain {s : σ →₀ ℕ} {c : R} :
    (monomial (s.mapDomain f) c).killCompl hf = monomial s c := by
  simp [← MvPolynomial.rename_monomial]

