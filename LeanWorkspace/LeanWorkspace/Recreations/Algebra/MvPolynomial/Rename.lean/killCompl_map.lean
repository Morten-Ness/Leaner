import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

theorem killCompl_map (φ : R →+* S) (p : MvPolynomial τ R) :
    (p.map φ).killCompl hf = (p.killCompl hf).map φ := by
  simp only [← AlgHom.coe_toRingHom, ← RingHom.comp_apply]
  congr
  ext i n
  · simp
  · by_cases h : i ∈ Set.range f <;> simp [MvPolynomial.killCompl, h]

