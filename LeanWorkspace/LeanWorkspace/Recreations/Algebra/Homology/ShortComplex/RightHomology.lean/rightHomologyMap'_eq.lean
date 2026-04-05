import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

theorem rightHomologyMap'_eq : CategoryTheory.ShortComplex.rightHomologyMap' φ h₁ h₂ = γ.φH := CategoryTheory.ShortComplex.RightHomologyMapData.congr_φH (Subsingleton.elim _ _)

