import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasRightHomology]

theorem opcycles_ext_iff {A : C} (f₁ f₂ : S.opcycles ⟶ A) :
    f₁ = f₂ ↔ S.pOpcycles ≫ f₁ = S.pOpcycles ≫ f₂ := by
  rw [cancel_epi]

