import Mathlib

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]

variable {S₁ S₂ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

variable (a : R)

theorem rightHomologyMap'_smul :
    rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).rightHomologyMap'_eq, RightHomologyMapData.smul_φH, γ.rightHomologyMap'_eq]

