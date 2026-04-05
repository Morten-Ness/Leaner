import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C]
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

theorem flip_flip (K : HomologicalComplex₂ C c₁ c₂) : K.flip.flip = K := rfl

