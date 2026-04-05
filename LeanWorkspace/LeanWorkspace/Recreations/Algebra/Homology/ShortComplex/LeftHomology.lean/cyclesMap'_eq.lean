import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

theorem cyclesMap'_eq : CategoryTheory.ShortComplex.cyclesMap' φ h₁ h₂ = γ.φK := CategoryTheory.ShortComplex.LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

