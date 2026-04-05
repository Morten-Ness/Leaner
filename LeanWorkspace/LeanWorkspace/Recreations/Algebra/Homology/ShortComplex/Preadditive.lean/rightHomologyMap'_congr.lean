import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable (φ₁ φ₂ φ₃ φ₄ : S₁ ⟶ S₂)

theorem rightHomologyMap'_congr (h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : rightHomologyMap' φ₁ h₁ h₂ = rightHomologyMap' φ₂ h₁ h₂ := by
  rw [CategoryTheory.ShortComplex.Homotopy.eq_add_nullHomotopic h, CategoryTheory.ShortComplex.rightHomologyMap'_add, CategoryTheory.ShortComplex.rightHomologyMap'_nullHomotopic, add_zero]

