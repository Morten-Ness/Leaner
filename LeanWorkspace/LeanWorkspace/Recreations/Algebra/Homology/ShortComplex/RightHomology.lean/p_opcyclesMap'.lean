import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)

theorem p_opcyclesMap' : h₁.p ≫ CategoryTheory.ShortComplex.opcyclesMap' φ h₁ h₂ = φ.τ₂ ≫ h₂.p := RightHomologyMapData.commp _

