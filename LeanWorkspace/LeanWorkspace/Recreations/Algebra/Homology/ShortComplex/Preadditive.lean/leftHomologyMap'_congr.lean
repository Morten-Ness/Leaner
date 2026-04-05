import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable (φ₁ φ₂ φ₃ φ₄ : S₁ ⟶ S₂)

theorem leftHomologyMap'_congr (h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : leftHomologyMap' φ₁ h₁ h₂ = leftHomologyMap' φ₂ h₁ h₂ := by
  rw [CategoryTheory.ShortComplex.Homotopy.eq_add_nullHomotopic h, CategoryTheory.ShortComplex.leftHomologyMap'_add, CategoryTheory.ShortComplex.leftHomologyMap'_nullHomotopic, add_zero]

