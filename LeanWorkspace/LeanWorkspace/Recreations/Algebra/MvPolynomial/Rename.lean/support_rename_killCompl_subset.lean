import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem support_rename_killCompl_subset {p : MvPolynomial τ R} {f : σ → τ} (hf : f.Injective) :
    ((p.killCompl hf).rename f).support ⊆ p.support := by
  classical
  rw [MvPolynomial.support_rename_of_injective hf, MvPolynomial.support_killCompl, Finset.image_preimage]
  exact Finset.filter_subset ..

