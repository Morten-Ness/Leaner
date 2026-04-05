import Mathlib

variable {R : Type u} [CommRing R]

variable {M₁ M₂ M₃ M₄ : ModuleCat.{u} R}

theorem tensor_ext₃ {f g : M₁ ⊗ (M₂ ⊗ M₃) ⟶ M₄}
    (h : ∀ m₁ m₂ m₃, f (m₁ ⊗ₜ (m₂ ⊗ₜ m₃)) = g (m₁ ⊗ₜ (m₂ ⊗ₜ m₃))) :
    f = g := by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact ModuleCat.MonoidalCategory.tensor_ext₃' h

