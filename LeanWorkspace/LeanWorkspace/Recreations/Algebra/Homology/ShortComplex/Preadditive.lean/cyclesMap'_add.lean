import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

theorem cyclesMap'_add :
    cyclesMap' (φ + φ') h₁ h₂ = cyclesMap' φ h₁ h₂ +
      cyclesMap' φ' h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ'.cyclesMap'_eq,
    (γ.add γ').cyclesMap'_eq, LeftHomologyMapData.add_φK]

