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

include hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hc₁ hc₂ hc₃ hc₄ in
theorem bijective_of_surjective_of_bijective_of_bijective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Bijective i₂) (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) :
    Function.Bijective i₃ := ⟨MonoidHom.injective_of_surjective_of_injective_of_injective f₁ f₂ f₃ g₁ g₂ g₃ i₁ i₂ i₃ i₄
      hc₁ hc₂ hc₃ hf₁ hf₂ hg₁ hi₁ hi₂.1 hi₄.1,
    MonoidHom.surjective_of_surjective_of_surjective_of_injective f₂ f₃ f₄ g₂ g₃ g₄ i₂ i₃ i₄ i₅
      hc₂ hc₃ hc₄ hf₃ hg₂ hg₃ hi₂.2 hi₄.2 hi₅⟩

