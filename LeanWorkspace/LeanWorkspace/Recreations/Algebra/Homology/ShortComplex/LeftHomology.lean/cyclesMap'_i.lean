import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

theorem cyclesMap'_i : CategoryTheory.ShortComplex.cyclesMap' φ h₁ h₂ ≫ h₂.i = h₁.i ≫ φ.τ₂ := LeftHomologyMapData.commi _

