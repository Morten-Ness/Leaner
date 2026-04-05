import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

theorem cycles_ext {A : C} (f₁ f₂ : A ⟶ S.cycles) (h : f₁ ≫ S.iCycles = f₂ ≫ S.iCycles) :
    f₁ = f₂ := by
  simpa only [CategoryTheory.ShortComplex.cycles_ext_iff] using h

