import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

theorem leftHomologyMap'_eq : CategoryTheory.ShortComplex.leftHomologyMap' φ h₁ h₂ = γ.φH := CategoryTheory.ShortComplex.LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

