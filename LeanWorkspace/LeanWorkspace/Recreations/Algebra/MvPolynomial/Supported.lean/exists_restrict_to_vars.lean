import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem exists_restrict_to_vars (R : Type*) [CommRing R] {F : MvPolynomial σ ℤ}
    (hF : ↑F.vars ⊆ s) : ∃ f : (s → R) → R, ∀ x : σ → R, f (x ∘ (↑) : s → R) = aeval x F := by
  rw [← MvPolynomial.mem_supported, MvPolynomial.supported_eq_range_rename, AlgHom.mem_range] at hF
  obtain ⟨F', hF'⟩ := hF
  use fun z ↦ aeval z F'
  intro x
  simp only [← hF', aeval_rename]

