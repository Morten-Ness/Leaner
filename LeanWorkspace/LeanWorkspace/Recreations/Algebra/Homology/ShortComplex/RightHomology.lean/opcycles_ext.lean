import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasRightHomology]

theorem opcycles_ext {A : C} (f₁ f₂ : S.opcycles ⟶ A)
    (h : S.pOpcycles ≫ f₁ = S.pOpcycles ≫ f₂) : f₁ = f₂ := by
  simpa only [CategoryTheory.ShortComplex.opcycles_ext_iff]

