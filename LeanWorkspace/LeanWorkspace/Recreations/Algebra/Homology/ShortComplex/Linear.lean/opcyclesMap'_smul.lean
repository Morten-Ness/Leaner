import Mathlib

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]

variable {S₁ S₂ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

variable (a : R)

theorem opcyclesMap'_smul :
    opcyclesMap' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).opcyclesMap'_eq, RightHomologyMapData.smul_φQ, γ.opcyclesMap'_eq]

