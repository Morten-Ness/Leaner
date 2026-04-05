import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

theorem leftHomology_ext {A : C} (f₁ f₂ : S.leftHomology ⟶ A)
    (h : S.leftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂) : f₁ = f₂ := by
  simpa only [CategoryTheory.ShortComplex.leftHomology_ext_iff] using h

