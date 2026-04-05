import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem leftHomologyMap'_op
    (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    (leftHomologyMap' φ h₁ h₂).op = CategoryTheory.ShortComplex.rightHomologyMap' (opMap φ) h₂.op h₁.op := by
  let γ : LeftHomologyMapData φ h₁ h₂ := leftHomologyMapData φ h₁ h₂
  simp only [γ.leftHomologyMap'_eq, γ.CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq CategoryTheory.ShortComplex.RightHomologyData.op,
    LeftHomologyMapData.op_φH]

