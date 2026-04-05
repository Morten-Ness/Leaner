import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

theorem leftHomologyπ_naturality' :
    h₁.π ≫ CategoryTheory.ShortComplex.leftHomologyMap' φ h₁ h₂ = CategoryTheory.ShortComplex.cyclesMap' φ h₁ h₂ ≫ h₂.π := LeftHomologyMapData.commπ _

