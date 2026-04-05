import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable (φ₁ φ₂ φ₃ φ₄ : S₁ ⟶ S₂)

theorem homologyMap'_congr (h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂) (h₁ : S₁.HomologyData)
    (h₂ : S₂.HomologyData) : homologyMap' φ₁ h₁ h₂ = homologyMap' φ₂ h₁ h₂ := by
  rw [CategoryTheory.ShortComplex.Homotopy.eq_add_nullHomotopic h, CategoryTheory.ShortComplex.homologyMap'_add, CategoryTheory.ShortComplex.homologyMap'_nullHomotopic, add_zero]

