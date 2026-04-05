import Mathlib

variable {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : Type*}

variable [Group M₁] [Group M₂] [Group M₃] [Group M₄] [Group M₅]

variable [Group N₁] [Group N₂] [Group N₃] [Group N₄] [Group N₅]

variable (f₁ : M₁ →* M₂) (f₂ : M₂ →* M₃) (f₃ : M₃ →* M₄) (f₄ : M₄ →* M₅)

variable (g₁ : N₁ →* N₂) (g₂ : N₂ →* N₃) (g₃ : N₃ →* N₄) (g₄ : N₄ →* N₅)

variable (i₁ : M₁ →* N₁) (i₂ : M₂ →* N₂) (i₃ : M₃ →* N₃) (i₄ : M₄ →* N₄)
  (i₅ : M₅ →* N₅)

variable (hc₁ : g₁.comp i₁ = i₂.comp f₁) (hc₂ : g₂.comp i₂ = i₃.comp f₂)
  (hc₃ : g₃.comp i₃ = i₄.comp f₃) (hc₄ : g₄.comp i₄ = i₅.comp f₄)

variable (hf₁ : Function.MulExact f₁ f₂) (hf₂ : Function.MulExact f₂ f₃)
  (hf₃ : Function.MulExact f₃ f₄) (hg₁ : Function.MulExact g₁ g₂)
  (hg₂ : Function.MulExact g₂ g₃) (hg₃ : Function.MulExact g₃ g₄)

include hf₁ hg₁ hc₁ hc₂ in
theorem surjective_of_surjective_of_injective_of_left_exact (hi₂ : Function.Surjective i₂)
    (hi₃ : Function.Injective i₃) (hg₀ : Function.Injective g₁) : Function.Surjective i₁ := by
  refine MonoidHom.surjective_of_surjective_of_surjective_of_injective (1 : Unit →* M₁) f₁ f₂ (1 : Unit →* N₁)
    g₁ g₂ 1 i₁ i₂ i₃ (by simp) hc₁ hc₂ hf₁ (fun y ↦ ?_) hg₁ (fun | .unit => ⟨0, rfl⟩) hi₂ hi₃
  simp only [Set.mem_range, one_apply, exists_const]
  exact ⟨fun h ↦ (hg₀ ((map_one _).trans h.symm)), fun h ↦ h ▸ (map_one _)⟩

