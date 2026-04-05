import Mathlib

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]

variable {S₁ S₂ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

variable (a : R)

theorem leftHomologyMap'_smul :
    leftHomologyMap' (a • φ) h₁ h₂ = a • leftHomologyMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).leftHomologyMap'_eq, LeftHomologyMapData.smul_φH, γ.leftHomologyMap'_eq]

