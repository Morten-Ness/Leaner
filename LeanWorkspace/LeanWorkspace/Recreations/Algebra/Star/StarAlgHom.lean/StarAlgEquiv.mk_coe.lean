import Mathlib

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

theorem mk_coe (e : A ≃⋆ₐ[R] B) (e' h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A ≃⋆ₐ[R] B) = e := StarAlgEquiv.ext fun _ => rfl

