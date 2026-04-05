import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C]
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

theorem toGradedObjectMap_apply {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) (i₁ : I₁) (i₂ : I₂) :
    HomologicalComplex₂.toGradedObjectMap φ ⟨i₁, i₂⟩ = (φ.f i₁).f i₂ := rfl

