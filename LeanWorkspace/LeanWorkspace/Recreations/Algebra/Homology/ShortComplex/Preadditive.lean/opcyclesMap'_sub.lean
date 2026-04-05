import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

theorem opcyclesMap'_sub :
    opcyclesMap' (φ - φ') h₁ h₂ = opcyclesMap' φ h₁ h₂ -
      opcyclesMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, CategoryTheory.ShortComplex.opcyclesMap'_add, CategoryTheory.ShortComplex.opcyclesMap'_neg]

