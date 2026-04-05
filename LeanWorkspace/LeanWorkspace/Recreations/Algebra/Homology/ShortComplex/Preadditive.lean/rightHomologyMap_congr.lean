import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable (φ₁ φ₂ φ₃ φ₄ : S₁ ⟶ S₂)

theorem rightHomologyMap_congr (h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomologyMap φ₁ = rightHomologyMap φ₂ := CategoryTheory.ShortComplex.Homotopy.rightHomologyMap'_congr h _ _

