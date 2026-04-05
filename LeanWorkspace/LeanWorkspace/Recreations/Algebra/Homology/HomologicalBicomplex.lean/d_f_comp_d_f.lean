import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C]
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

theorem d_f_comp_d_f (K : HomologicalComplex₂ C c₁ c₂)
    (i₁ i₁' i₁'' : I₁) (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.d i₁' i₁'').f i₂ = 0 := by
  rw [← comp_f, d_comp_d, zero_f]

