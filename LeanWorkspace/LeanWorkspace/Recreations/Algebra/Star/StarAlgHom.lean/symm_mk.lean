import Mathlib

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A ≃⋆ₐ[R] B).symm =
      { symm_mk.aux f f' h₁ h₂ h₃ h₄ h₅ h₆ with
        toFun := f'
        invFun := f } :=
  rfl

