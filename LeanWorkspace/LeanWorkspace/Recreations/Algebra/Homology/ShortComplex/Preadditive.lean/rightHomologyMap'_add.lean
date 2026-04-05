import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

theorem rightHomologyMap'_add :
    rightHomologyMap' (φ + φ') h₁ h₂ = rightHomologyMap' φ h₁ h₂ +
      rightHomologyMap' φ' h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ'.rightHomologyMap'_eq,
    (γ.add γ').rightHomologyMap'_eq, RightHomologyMapData.add_φH]

