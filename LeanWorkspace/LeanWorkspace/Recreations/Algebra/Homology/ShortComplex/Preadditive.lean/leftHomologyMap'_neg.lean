import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

theorem leftHomologyMap'_neg :
    leftHomologyMap' (-φ) h₁ h₂ = -leftHomologyMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ.neg.leftHomologyMap'_eq, LeftHomologyMapData.neg_φH]

