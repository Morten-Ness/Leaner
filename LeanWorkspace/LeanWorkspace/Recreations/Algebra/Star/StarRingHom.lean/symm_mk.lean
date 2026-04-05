import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B).symm =
      { symm_mk.aux f f' h₁ h₂ h₃ h₄ h₅ with
        toFun := f'
        invFun := f } :=
  rfl

