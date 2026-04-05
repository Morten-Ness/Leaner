import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_sigma {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : Sigma σ → β) :
    ∏ x ∈ s.sigma t, f x = ∏ a ∈ s, ∏ s ∈ t a, f ⟨a, s⟩ := by
  simp_rw [← disjiUnion_map_sigma_mk, prod_disjiUnion, prod_map, Function.Embedding.sigmaMk_apply]

