import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

theorem opcyclesMap'_eq : CategoryTheory.ShortComplex.opcyclesMap' φ h₁ h₂ = γ.φQ := CategoryTheory.ShortComplex.RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

