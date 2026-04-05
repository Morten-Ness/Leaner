import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem opcyclesMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (h₃ : S₃.RightHomologyData) :
    CategoryTheory.ShortComplex.opcyclesMap' (φ₁ ≫ φ₂) h₁ h₃ = CategoryTheory.ShortComplex.opcyclesMap' φ₁ h₁ h₂ ≫ CategoryTheory.ShortComplex.opcyclesMap' φ₂ h₂ h₃ := by
  let γ₁ := CategoryTheory.ShortComplex.rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := CategoryTheory.ShortComplex.rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.opcyclesMap'_eq, γ₂.opcyclesMap'_eq, CategoryTheory.ShortComplex.RightHomologyMapData.opcyclesMap'_eq (γ₁.comp γ₂),
    RightHomologyMapData.comp_φQ]

