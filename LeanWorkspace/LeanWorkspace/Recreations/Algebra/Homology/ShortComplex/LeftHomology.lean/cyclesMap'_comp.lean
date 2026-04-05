import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem cyclesMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    CategoryTheory.ShortComplex.cyclesMap' (φ₁ ≫ φ₂) h₁ h₃ = CategoryTheory.ShortComplex.cyclesMap' φ₁ h₁ h₂ ≫ CategoryTheory.ShortComplex.cyclesMap' φ₂ h₂ h₃ := by
  let γ₁ := CategoryTheory.ShortComplex.leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := CategoryTheory.ShortComplex.leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.cyclesMap'_eq, γ₂.cyclesMap'_eq, CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq (γ₁.comp γ₂),
    LeftHomologyMapData.comp_φK]

