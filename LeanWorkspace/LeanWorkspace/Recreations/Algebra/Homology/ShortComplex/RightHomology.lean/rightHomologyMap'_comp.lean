import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem rightHomologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (h₃ : S₃.RightHomologyData) :
    CategoryTheory.ShortComplex.rightHomologyMap' (φ₁ ≫ φ₂) h₁ h₃ = CategoryTheory.ShortComplex.rightHomologyMap' φ₁ h₁ h₂ ≫
      CategoryTheory.ShortComplex.rightHomologyMap' φ₂ h₂ h₃ := by
  let γ₁ := CategoryTheory.ShortComplex.rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := CategoryTheory.ShortComplex.rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.rightHomologyMap'_eq, γ₂.rightHomologyMap'_eq, CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq (γ₁.comp γ₂),
    RightHomologyMapData.comp_φH]

