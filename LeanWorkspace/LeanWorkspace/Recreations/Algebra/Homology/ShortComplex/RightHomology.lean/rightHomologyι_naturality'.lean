import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)

theorem rightHomologyι_naturality' :
    CategoryTheory.ShortComplex.rightHomologyMap' φ h₁ h₂ ≫ h₂.ι = h₁.ι ≫ CategoryTheory.ShortComplex.opcyclesMap' φ h₁ h₂ := RightHomologyMapData.commι _

