import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem coeff_rename_eq_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
    (h : ∀ u : σ →₀ ℕ, u.mapDomain f = d → φ.coeff u = 0) : (MvPolynomial.rename f φ).coeff d = 0 := by
  classical
  rw [MvPolynomial.rename_eq, ← notMem_support_iff]
  intro H
  replace H := mapDomain_support H
  rw [Finset.mem_image] at H
  obtain ⟨u, hu, rfl⟩ := H
  specialize h u rfl
  rw [Finsupp.mem_support_iff] at hu
  contradiction

