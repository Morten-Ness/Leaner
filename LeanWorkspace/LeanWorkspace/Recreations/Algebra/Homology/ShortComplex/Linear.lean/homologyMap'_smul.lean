import Mathlib

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]

variable {S₁ S₂ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}

variable (a : R)

theorem homologyMap'_smul :
    homologyMap' (a • φ) h₁ h₂ = a • homologyMap' φ h₁ h₂ := CategoryTheory.ShortComplex.leftHomologyMap'_smul _ _ _ _

