import Mathlib

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]

variable {S₁ S₂ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

variable (a : R)

theorem cyclesMap'_smul :
    cyclesMap' (a • φ) h₁ h₂ = a • cyclesMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).cyclesMap'_eq, LeftHomologyMapData.smul_φK, γ.cyclesMap'_eq]

