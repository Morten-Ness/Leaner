import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem leftHomologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    CategoryTheory.ShortComplex.leftHomologyMap' (φ₁ ≫ φ₂) h₁ h₃ = CategoryTheory.ShortComplex.leftHomologyMap' φ₁ h₁ h₂ ≫
      CategoryTheory.ShortComplex.leftHomologyMap' φ₂ h₂ h₃ := by
  let γ₁ := CategoryTheory.ShortComplex.leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := CategoryTheory.ShortComplex.leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.leftHomologyMap'_eq, γ₂.leftHomologyMap'_eq, CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq (γ₁.comp γ₂),
    LeftHomologyMapData.comp_φH]

