import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C]
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

variable (K : HomologicalComplex₂ C c₁ c₂)

theorem XXIsoOfEq_rfl (i₁ : I₁) (i₂ : I₂) :
    K.XXIsoOfEq _ _ _ (rfl : i₁ = i₁) (rfl : i₂ = i₂) = Iso.refl _ := rfl

