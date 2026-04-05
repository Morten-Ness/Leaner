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

include hf₂ hg₁ hg₂ hc₁ hc₂ hc₃ in
theorem surjective_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) :
    Function.Surjective i₂ := by
  intro x
  obtain ⟨y, hy⟩ := hi₃ (g₂ x)
  obtain ⟨a, rfl⟩ : y ∈ Set.range f₂ := (hf₂ _).mp <| by
    simpa [hy, hg₂.apply_apply_eq_one, map_eq_one_iff _ hi₄] using (DFunLike.congr_fun hc₃ y).symm
  obtain ⟨b, hb⟩ : x / i₂ a ∈ Set.range g₁ := (hg₁ _).mp <| by
    simp [← hy, show g₂ (i₂ a) = i₃ (f₂ a) by simpa using DFunLike.congr_fun hc₂ a]
  obtain ⟨o, rfl⟩ := hi₁ b
  use f₁ o * a
  simp [← show g₁ (i₁ o) = i₂ (f₁ o) by simpa using DFunLike.congr_fun hc₁ o, hb]

