import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_eq_zero_iff_of_injective (p : MvPolynomial σ R) {f : σ → τ}
    (hf : f.Injective) : p.rename f = 0 ↔ p = 0 := by
  rw [← MvPolynomial.rename_zero f, (MvPolynomial.rename_injective _ hf).eq_iff]

