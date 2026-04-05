import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

variable {p} (φ : MvPolynomial σ R)

theorem coeff_expand_of_not_dvd {m : σ →₀ ℕ} {i : σ} (h : ¬ p ∣ m i) :
    (MvPolynomial.expand p φ).coeff m = 0 := by
  classical
  contrapose! h
  grw [← mem_support_iff, MvPolynomial.support_expand_subset, Finset.mem_image] at h
  rcases h with ⟨a, -, rfl⟩
  exact ⟨a i, by simp⟩

