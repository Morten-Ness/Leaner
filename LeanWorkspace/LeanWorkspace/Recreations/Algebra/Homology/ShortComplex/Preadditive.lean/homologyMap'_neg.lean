import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}

theorem homologyMap'_neg :
    homologyMap' (-φ) h₁ h₂ = -homologyMap' φ h₁ h₂ := CategoryTheory.ShortComplex.leftHomologyMap'_neg _ _

