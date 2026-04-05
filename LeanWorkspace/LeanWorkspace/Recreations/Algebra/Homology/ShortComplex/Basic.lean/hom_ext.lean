import Mathlib

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

variable (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃) : f = g := Hom.ext h₁ h₂ h₃

